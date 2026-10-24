#!/usr/bin/env python3
"""
antivenom.py - turn a crochet pattern web page (saved with the SingleFile browser
extension) into a Markdown file and a nicely laid-out PDF, with the images pulled
out into a subfolder.

Setup (once)
------------
    pip install beautifulsoup4 lxml reportlab

Usage
-----
    python antivenom.py vulpes-the-fox.html

Put the saved page and its photos file side by side with the SAME name:

    vulpes-the-fox.html     <- the saved page
    vulpes-the-fox.json     <- step photos (optional; made by the browser-console snippet)

The .json is picked up automatically when it sits next to the .html with the same
name. Output goes to ./patterns/ (change with -o):

    patterns/
        vulpes-the-fox.md
        vulpes-the-fox.pdf
        images/vulpes-the-fox/cover-01.jpg, measurements-01.jpg, step-01.png, ...

Live progress is shown for every stage (with an estimated time left). The only timers are
network timeouts (20 s) and a stop after 5 failed downloads in a row; photos are never resized
and nothing else is cut off, so a big pattern simply takes as long as it takes (Ctrl+C stops it).

Options: -o DIR (output folder), --label Row (say "Row 1:" instead of "Rnd 1:"),
--no-pdf (Markdown only). Everything else is automatic. One page per run; to do
several:   for f in *.html; do python antivenom.py "$f"; done

The Markdown never contains base64 data: images are written to disk and referenced
as ![alt](images/<pattern>/<file>) where they appeared. The PDF only shows what the
saved page actually contains - nothing is derived or invented.

What is (and isn't) in the saved HTML
-------------------------------------
Embedded in the file, so extracted:  cover photos, measurement photos, and any
step photo that was expanded on the page when you saved it.
NOT in the file: the per-step photos behind the little camera icons. They are
fetched from the site's server only when you click the icon, so the saved page
never contains them. The .json lists where they live; the script downloads them.
Without a .json, the Markdown gets a short text marker where a photo existed.

Photos JSON format
------------------
    {"title": "Vulpes the fox",
     "referer": "https://...",          # optional, sent when downloading
     "photos": {"12": "https://.../a.png", "31": "https://.../b.png"}}
Keys are step numbers (the page's li12, li31, ...). Values are URLs or local
file paths (relative paths are resolved next to the JSON file).
"""

import argparse
import base64
import hashlib
import json
import os
import re
import sys
import time
import urllib.request
from pathlib import Path

from bs4 import BeautifulSoup, NavigableString, Tag

try:  # lxml is faster and more forgiving; fall back to the stdlib parser
    import lxml  # noqa: F401
    PARSER = "lxml"
except ImportError:  # pragma: no cover
    PARSER = "html.parser"

DOWNLOAD_TIMEOUT = 20            # seconds a network operation may stall (connect / each read)
MAX_FAILURES_IN_A_ROW = 5        # then stop trying (offline / blocked) instead of crawling on


def _fmt_secs(t):
    t = int(round(t))
    return f"{t // 60}m {t % 60:02d}s" if t >= 60 else f"{t}s"


class Progress:
    """Live 'label done/total (eta)' line: redraws in place on a terminal, and prints
    roughly every 10% when output is piped to a file."""

    def __init__(self, label, total):
        self.label, self.total, self.t0, self.done = label, total, time.monotonic(), 0

    def _text(self, done):
        txt = f"[info] {self.label} {done}/{self.total}"
        if 0 < done < self.total:
            left = (time.monotonic() - self.t0) / done * (self.total - done)
            txt += f"  (about {_fmt_secs(left)} left)"
        return txt

    def update(self, done=None):
        self.done = self.done + 1 if done is None else done
        if sys.stderr.isatty():
            print("\r" + self._text(self.done).ljust(78), end="", file=sys.stderr, flush=True)
        elif self.total and self.done < self.total and self.done % max(5, self.total // 10) == 0:
            print(self._text(self.done), file=sys.stderr, flush=True)

    def finish(self, text=None):
        took = _fmt_secs(time.monotonic() - self.t0)
        msg = (text or f"[info] {self.label} {self.done}/{self.total}") + f"  [{took}]"
        if sys.stderr.isatty():
            print("\r" + msg.ljust(78), file=sys.stderr, flush=True)
        else:
            print(msg, file=sys.stderr, flush=True)


def _status(msg, final=False):
    """One-off status line (in place on a terminal)."""
    if sys.stderr.isatty():
        print("\r" + msg.ljust(78), end="\n" if final else "", file=sys.stderr, flush=True)
    elif final:
        print(msg, file=sys.stderr, flush=True)


PHOTO_MARKER = "*[step photo not included in the saved page]*"
VIDEO_MARKER = "*[video not included in the saved page]*"

MIME_EXT = {
    "image/jpeg": ".jpg", "image/jpg": ".jpg", "image/png": ".png",
    "image/webp": ".webp", "image/gif": ".gif",
}
DATA_URI = re.compile(r"^data:(image/[a-z0-9.+-]+);base64,(.+)$", re.I | re.S)


# --------------------------------------------------------------------------
# small text helpers
# --------------------------------------------------------------------------
def slugify(text):
    text = re.sub(r"[^\w\s-]", "", text.lower(), flags=re.UNICODE)
    return re.sub(r"[\s_-]+", "-", text).strip("-") or "pattern"


def esc(text):
    """Escape characters that crochet notation would otherwise turn into
    Markdown formatting (e.g. '* ... *' repeat markers become italics)."""
    return (text.replace("\\", "\\\\").replace("*", "\\*")
                .replace("_", "\\_").replace("`", "\\`"))


def esc_line_start(line):
    """Stop '1) ...' / '2. ...' / '- ...' / '# ...' lines becoming lists/headings."""
    line = re.sub(r"^(\s*)(\d+)([.)])", r"\1\2\\\3", line)
    return re.sub(r"^(\s*)([-+#>])(\s)", r"\1\\\2\3", line)


def tidy(text):
    """Collapse whitespace but keep explicit line breaks ('\\n')."""
    text = text.replace("\xa0", " ").replace("\u200b", "")
    text = re.sub(r"[ \t\r\f\v]+", " ", text)
    text = re.sub(r" ?\n ?", "\n", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def plain(node):
    return tidy(node.get_text(" ")) if node else ""


# --------------------------------------------------------------------------
# HTML -> Markdown (inline / block)
# --------------------------------------------------------------------------
def inline(node):
    """Markdown for a node's inline content. Spaces are taken from the source
    HTML as-is, so '6<span>sc</span>' stays '6sc' like on the site."""
    if isinstance(node, NavigableString):
        return esc(str(node))
    if not isinstance(node, Tag):
        return ""
    name = node.name
    if name == "br":
        return "\n"
    if name in ("img", "svg", "script", "style", "template", "sl-icon"):
        return ""
    cls = node.get("class") or []
    if "line-icons" in cls:  # camera / video icons: handled separately
        return ""
    inner = "".join(inline(c) for c in node.children)
    if name in ("b", "strong") and inner.strip():
        return f"**{inner.strip()}**"
    if name in ("i", "em") and inner.strip():
        return f"*{inner.strip()}*"
    if name == "a" and node.get("href") and inner.strip():
        return f"[{inner.strip()}]({node['href']})"
    return inner


def inline_clean(node):
    """Inline markdown for a whole cell/paragraph, with hard line breaks."""
    text = tidy(inline(node))
    return "  \n".join(esc_line_start(ln) for ln in text.split("\n"))


BLOCK_TAGS = {"p", "div", "ul", "ol", "li", "h1", "h2", "h3", "h4", "h5", "h6",
              "table", "blockquote"}


def blocks(node):
    """Convert a free-text container (About / Measurements) to a list of
    Markdown paragraphs."""
    out, buf = [], []

    def flush():
        text = tidy("".join(buf))
        buf.clear()
        for para in re.split(r"\n\s*\n", text):
            para = para.strip()
            if para:
                out.append("  \n".join(esc_line_start(ln) for ln in para.split("\n")))

    for ch in node.children:
        if isinstance(ch, NavigableString):
            buf.append(esc(str(ch)))
        elif ch.name in ("ul", "ol"):
            flush()
            for n, li in enumerate(ch.find_all("li", recursive=False), 1):
                mark = f"{n}." if ch.name == "ol" else "-"
                text = tidy(inline(li)).replace("\n", " ")
                if text:
                    out.append(f"{mark} {text}")
        elif ch.name in ("h1", "h2", "h3", "h4", "h5", "h6"):
            flush()
            out.append(f"**{tidy(inline(ch))}**")
        elif ch.name in BLOCK_TAGS:
            flush()
            out.extend(blocks(ch))
        else:
            buf.append(inline(ch))
    flush()
    return out


# --------------------------------------------------------------------------
# image extraction
# --------------------------------------------------------------------------
class ImageStore:
    def __init__(self, out_dir, slug):
        self.dir = out_dir / "images" / slug
        self.rel = f"images/{slug}"
        self.seen = {}          # sha1 -> relative path
        self.counters = {}
        self.referer = None     # optional, taken from the photos JSON
        self.failed = []        # (source, error) for step photos that couldn't be fetched
        self.total = 0          # number of step photos we'll try to get (for the progress line)
        self.progress = None
        self.attempts = 0
        self.downloaded = 0
        self.fail_streak = 0
        self.gave_up = False

    def save(self, img_tag, kind):
        """Write an <img> with an embedded data: URI to disk.
        Returns the relative path, or None if it can't be extracted."""
        m = DATA_URI.match((img_tag.get("src") or "").strip())
        if not m:
            return None
        mime, payload = m.group(1).lower(), m.group(2)
        ext = MIME_EXT.get(mime)
        if not ext:
            return None
        try:
            data = base64.b64decode(payload)
        except Exception:
            return None
        return self.save_bytes(data, ext, kind)

    def save_bytes(self, data, ext, kind):
        digest = hashlib.sha1(data).hexdigest()
        if digest in self.seen:
            return self.seen[digest]
        self.counters[kind] = self.counters.get(kind, 0) + 1
        name = f"{kind}-{self.counters[kind]:02d}{ext}"
        self.dir.mkdir(parents=True, exist_ok=True)
        (self.dir / name).write_bytes(data)
        rel = f"{self.rel}/{name}"
        self.seen[digest] = rel
        return rel

    def download(self, src, kind="step"):
        """Get a step photo from a URL or a local file path.
        Returns the relative path, or None on failure. After MAX_FAILURES_IN_A_ROW
        failures in a row it stops trying the rest (offline / blocked)."""
        if self.gave_up:
            self.failed.append((src, "skipped after repeated failures"))
            return None
        self.attempts += 1
        if self.total:
            if self.progress is None:
                self.progress = Progress("downloading step photos", self.total)
            self.progress.update(self.attempts)
        try:
            if re.match(r"https?://", src):
                headers = {"User-Agent": "Mozilla/5.0"}
                if self.referer:
                    headers["Referer"] = self.referer
                req = urllib.request.Request(src, headers=headers)
                with urllib.request.urlopen(req, timeout=DOWNLOAD_TIMEOUT) as r:
                    data = r.read()
                    ctype = r.headers.get("Content-Type", "").split(";")[0].strip().lower()
                ext = MIME_EXT.get(ctype) or Path(src.split("?")[0]).suffix.lower() or ".png"
            else:
                path = Path(src)
                data, ext = path.read_bytes(), path.suffix.lower() or ".png"
        except Exception as e:
            self.failed.append((src, str(e) or type(e).__name__))
            self.fail_streak += 1
            if self.fail_streak >= MAX_FAILURES_IN_A_ROW:
                self.gave_up = True
            return None
        self.fail_streak = 0
        self.downloaded += 1
        return self.save_bytes(data, ext, kind)


# --------------------------------------------------------------------------
# section extractors
# --------------------------------------------------------------------------
def cover_info(cover):
    """-> (list of (label, value), list of tags)"""
    info, tags, label = [], [], None
    for sec in cover.select(".cover-section"):
        for d in sec.find_all("div", recursive=False):
            cls = d.get("class") or []
            if "cover-title-label-crafter" in cls:
                label = plain(d)
            elif d.get("id") == "cover-tags":
                tags = [plain(t) for t in d.select(".cover-tags-user") if plain(t)]
            else:
                value = plain(d)
                if label and value:
                    info.append((label, value))
    return info, tags


def materials(container):
    """-> list of {"cat": str|None, "items": [{name, weight, text, hex, link}]}"""
    ul = container.select_one("ul.mat-table")
    if not ul:
        return []
    groups, current = [], None
    for ch in ul.find_all(recursive=False):
        if ch.name == "span" and ch.find("h2"):
            current = {"cat": plain(ch.find("h2")), "items": []}
            groups.append(current)
        elif ch.name == "li" and "mat-line" in (ch.get("class") or []):
            if current is None:
                current = {"cat": None, "items": []}
                groups.append(current)
            swatch = ch.select_one(".colorpicker-swatch")
            m = re.search(r"#[0-9a-fA-F]{3,8}", (swatch.get("style") or "") if swatch else "")
            item = ch.select_one(".mat_item")
            text = ""
            if item:
                clone = BeautifulSoup(str(item), PARSER)
                for w in clone.select(".mat_weight, .mat_link, .mat-link-icon-inline"):
                    w.decompose()
                text = tidy(inline(clone))
            link = item.select_one("[data-full_link]") if item else None
            current["items"].append({
                "name": plain(ch.select_one(".colorpicker-name")),
                "weight": plain(item.select_one(".mat_weight")) if item else "",
                "text": text,
                "hex": m.group(0) if m else "",
                "link": (link.get("data-full_link") if link else "") or "",
            })
    return [g for g in groups if g["items"]]


def abbreviations(container):
    rows = []
    for tr in container.select("table.abbr-table tr"):
        tds = tr.find_all("td", recursive=False)
        if len(tds) >= 2:
            abbr = (tds[0].get("data-abbr") or plain(tds[0])).strip()
            meaning = plain(tds[1])
            if abbr and meaning:
                rows.append((abbr, meaning))
    return rows


def has_icon(row_li, alt):
    return any(i.get("alt") == alt for i in row_li.select(".line-icons img"))



def format_label(label, word):
    """'2' -> 'Rnd 2', '4 to 5' / '2-46' -> 'Rnd 4 \u2013 5', anything else is left as is."""
    m = re.fullmatch(r"(\d+)\s*(?:-|\u2013|to)\s*(\d+)", label.strip())
    if m:
        return f"{word} {m.group(1)} \u2013 {m.group(2)}"
    if re.fullmatch(r"\d+[a-z]?", label.strip()):
        return f"{word} {label.strip()}"
    return label


def normalize_count(text):
    """Trailing stitch counts '(42)', '= 42', '= (42)' -> ' [42]' (already-bracketed stays)."""
    m = (re.search(r"\s*=?\s*[(\[](\d+)[)\]]\s*\.?\s*$", text)
         or re.search(r"\s*=\s*(\d+)\s*\.?\s*$", text))
    if m and text[:m.start()].strip():
        return f"{text[:m.start()]} [{m.group(1)}]"
    return text


def instructions(ul, images, markers=True, photo_urls=None, label_word="Rnd"):
    """Walk <ul id=ul_main> in document order.
    Returns (items, stats); every item is a dict with a "t" (type):
      section / sub / text      -> {"text"}
      round                     -> {"label", "text", "symbol"}   (symbol: note bullet)
      expanded                  -> {"label", "text"}             (unrolled copy that differs)
      image                     -> {"rel"}
      marker                    -> {"kind": photo|video, "indent"}"""
    photo_urls = photo_urls or {}
    items = []
    stats = {"rows": 0, "photos_saved": 0, "photo_markers": 0, "mismatch": 0}

    # lines whose photo is embedded (expanded on the page when it was saved)
    embedded_after = {li.get("data-line") for li in ul.find_all("li")
                      if li.get("data-ext") == "img"}

    def emit_row(li, table):
        cls = (table.get("class") or [""])[0]
        t2, t3 = table.select_one("td.t2"), table.select_one("td.t3")
        text = inline_clean(t3) if t3 else ""
        label = plain(t2)
        stats["rows"] += 1
        if cls == "SectionRow":
            items.append({"t": "section", "text": text})
        elif cls == "SubSectionRow":
            items.append({"t": "sub", "text": text})
        elif cls == "RndRow":
            if re.search(r"[0-9A-Za-z]", label):
                # drop a leading "3)" / "4)-5)" if it just repeats the label
                m = re.match(r"^\s*(\d+)\\?\)(?:\s*-\s*\d+\\?\))?\s*", text)
                n = re.match(r"\d+", label)
                if m and n and m.group(1) == n.group(0):
                    text = text[m.end():]
                items.append({"t": "round", "label": format_label(label, label_word),
                              "text": normalize_count(text), "symbol": False})
            else:  # symbol-style note marker such as a star
                items.append({"t": "round", "label": label, "text": text, "symbol": True})
        else:  # TextRow
            items.append({"t": "text", "text": text})

        rid = (li.get("id") or "")
        line_no = rid[2:] if rid.startswith("li") else None
        fetched = False
        if line_no in photo_urls and line_no not in embedded_after:
            rel = images.download(photo_urls[line_no])
            if rel:
                items.append({"t": "image", "rel": rel})
                stats["photos_saved"] += 1
                fetched = True
        if not markers:
            return
        indent = items[-1]["t"] == "round"
        if has_icon(li, "Click to see video"):
            items.append({"t": "marker", "kind": "video", "indent": indent})
            stats["photo_markers"] += 1
        if (not fetched and line_no not in embedded_after
                and has_icon(li, "Click to see photo")):
            items.append({"t": "marker", "kind": "photo", "indent": indent})
            stats["photo_markers"] += 1

    for ch in ul.find_all(recursive=False):
        if ch.name == "li" and ch.get("data-ext") == "img":
            img = ch.find("img")
            rel = images.save(img, "step") if img else None
            if rel:
                items.append({"t": "image", "rel": rel})
                stats["photos_saved"] += 1
            continue
        if ch.name == "li":
            tb = ch.find("table")   # rows without a table (ads etc.) are skipped
            if tb:
                emit_row(ch, tb)
        elif ch.name == "details":
            # A collapsed range row ("2-46"); the <li>s inside are its
            # unrolled copies, so only the summary row is emitted.
            summ = ch.find("summary")
            first = summ.find("table") if summ else None
            if first:
                emit_row(summ, first)
                base = plain(first.select_one("td.t3"))
                for inner in ch.find_all("li", recursive=False):
                    t3 = inner.select_one("td.t3")
                    if t3 and plain(t3) != base:
                        stats["mismatch"] += 1
                        items.append({"t": "expanded", "label": plain(inner.select_one("td.t2")),
                                      "text": inline_clean(t3)})
    return items, stats


# --------------------------------------------------------------------------
# Markdown rendering
# --------------------------------------------------------------------------
def items_to_md(items):
    """Instruction items -> Markdown lines (consecutive list rows stay tight)."""
    pieces = []   # (kind, text)
    for it in items:
        t = it["t"]
        if t == "section":
            pieces.append(("h", f"### {it['text']}"))
        elif t == "sub":
            pieces.append(("h", f"#### {it['text']}"))
        elif t == "text":
            pieces.append(("t", it["text"]))
        elif t == "round":
            if it["symbol"]:
                pieces.append(("r", f"- {it['label']} {it['text']}".rstrip()))
            else:
                pieces.append(("r", f"- **{esc(it['label'])}:** " + it["text"].replace("\n", "\n  ")))
        elif t == "image":
            pieces.append(("i", f"![step photo]({it['rel']})"))
        elif t == "marker":
            text = PHOTO_MARKER if it["kind"] == "photo" else VIDEO_MARKER
            pieces.append(("m", "  " + text) if it["indent"] else ("p", text))
        elif t == "expanded":
            pieces.append(("w", f"  - *(expanded row {it['label']}):* {it['text']}"))
    lines, prev = [], None
    for kind, text in pieces:
        if prev is not None and not (prev in ("r", "m", "w") and kind in ("r", "m", "w")):
            lines.append("")
        lines.append(text)
        prev = kind
    return lines


def render_md(d):
    title = d["title"]
    md = [f"# {esc(title)}", ""]
    if d["designer"]:
        md += [f"*{esc(d['designer'])}*", ""]
    for i, rel in enumerate(d["cover_imgs"], 1):
        md += [f"![{esc(title)} - cover photo {i}]({rel})", ""]
    if d["info"]:
        md += [f"- **{esc(k)}:** {esc(v)}" for k, v in d["info"]]
        md.append("")
    if d["tags"]:
        md += ["Tags: " + " ".join(esc(t) for t in d["tags"]), ""]
    if d["about"]:
        md += ["## About this pattern", ""]
        for b in d["about"]:
            md += [b, ""]
    if d["measure"]:
        md += ["## Measurements", ""]
        for b in d["measure"]["paras"]:
            md += [b, ""]
        for i, rel in enumerate(d["measure"]["imgs"], 1):
            md += [f"![measurements photo {i}]({rel})", ""]
    if d["materials"]:
        md += ["## Materials", ""]
        for g in d["materials"]:
            if g["cat"]:
                md += [f"### {esc(g['cat'])}", ""]
            for it in g["items"]:
                line = "- "
                if it["name"]:
                    line += f"**{esc(it['name'])}**: "
                if it["weight"]:
                    line += f"({esc(it['weight'])}) "
                line += it["text"]
                if it["hex"]:
                    line += f" - colour `{it['hex']}`"
                if it["link"]:
                    line += f" ([link]({it['link']}))"
                md.append(line.rstrip())
            md.append("")
    if d["items"] is not None:
        md += ["## Instructions", ""]
        md += items_to_md(d["items"]) + [""]
    if d["abbr"]:
        md += ["## Abbreviations", "", "| Abbreviation | Meaning |", "| --- | --- |"]

        def cell(s):
            return esc(s).replace("|", "\\|")
        md += [f"| {cell(a)} | {cell(b)} |" for a, b in d["abbr"]]
        md.append("")
    return re.sub(r"\n{3,}", "\n\n", "\n".join(md)).rstrip() + "\n"


# --------------------------------------------------------------------------
# one pattern file -> data model -> markdown (+ optional pdf)
# --------------------------------------------------------------------------
def convert(path, out_dir, markers=True, photo_urls=None, photo_title=None, referer=None,
            label_word="Rnd"):
    raw = path.read_text(encoding="utf-8", errors="replace")
    soup = BeautifulSoup(raw, PARSER)
    del raw
    for t in soup(["style", "script", "svg", "noscript", "template"]):
        t.decompose()

    page = soup.find(id="pageL")
    title_el = soup.find(id="title-cover")
    if not page or not title_el:
        raise ValueError("doesn't look like a saved pattern page "
                         "(no #pageL / #title-cover found)")
    title = plain(title_el)
    slug = slugify(title)
    images = ImageStore(out_dir, slug)
    images.referer = referer
    images.total = len(photo_urls or {})
    if photo_title and slugify(photo_title) != slug:
        print(f"[warn] the photos JSON is for '{photo_title}' but this page is "
              f"'{title}' - double-check you paired the right files", file=sys.stderr)

    cover = page.select_one(".wrapper-cover")
    d = {"title": title, "designer": plain(page.select_one("#designer-cover")),
         "cover_imgs": [], "info": [], "tags": [], "about": [], "measure": None,
         "materials": [], "abbr": [], "items": None}

    for img in cover.select(".pattern_image_cover img"):
        rel = images.save(img, "cover")
        if rel and rel not in d["cover_imgs"]:
            d["cover_imgs"].append(rel)
    d["info"], d["tags"] = cover_info(cover)

    about = page.select_one(".abbr-container .abbr-intro")
    if about and plain(about):
        d["about"] = blocks(about)

    meas = page.select_one(".measure_text")
    if meas:
        intro = meas.select_one(".abbr-intro")
        meas_imgs = []
        for img in meas.select("#measure_img_mobile img"):
            rel = images.save(img, "measurements")
            if rel and rel not in meas_imgs:
                meas_imgs.append(rel)
        if (intro and plain(intro)) or meas_imgs:
            d["measure"] = {"paras": blocks(intro) if intro else [], "imgs": meas_imgs}
        d["abbr"] = abbreviations(meas)

    mat = page.select_one(".materials_page_container")
    if mat:
        d["materials"] = materials(mat)

    ul = page.find(id="ul_main")
    stats = {"rows": 0, "photos_saved": 0, "photo_markers": 0, "mismatch": 0}
    if ul:
        d["items"], stats = instructions(ul, images, markers, photo_urls, label_word)

    out_path = out_dir / f"{slug}.md"
    out_path.write_text(render_md(d), encoding="utf-8")
    stats["images"] = len(images.seen)
    stats["photos_failed"] = len(images.failed)
    stats["gave_up"] = images.gave_up
    if images.progress:
        images.progress.finish(f"[info] step photos: {images.downloaded} downloaded, "
                               f"{len(images.failed)} failed")
    stats["first_error"] = images.failed[0] if images.failed else None
    return out_path, stats, d


# --------------------------------------------------------------------------
# PDF output
# --------------------------------------------------------------------------
# (regular path, bold file, italic file, bold-italic file) - first set that exists wins
_FONT_CANDIDATES = [
    ("/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf", "LiberationSans-Bold.ttf",
     "LiberationSans-Italic.ttf", "LiberationSans-BoldItalic.ttf"),
    ("/usr/share/fonts/liberation-sans/LiberationSans-Regular.ttf", "LiberationSans-Bold.ttf",
     "LiberationSans-Italic.ttf", "LiberationSans-BoldItalic.ttf"),
    ("/usr/share/fonts/liberation/LiberationSans-Regular.ttf", "LiberationSans-Bold.ttf",
     "LiberationSans-Italic.ttf", "LiberationSans-BoldItalic.ttf"),
    ("C:/Windows/Fonts/arial.ttf", "arialbd.ttf", "ariali.ttf", "arialbi.ttf"),
    ("/Library/Fonts/Arial.ttf", "Arial Bold.ttf", "Arial Italic.ttf", "Arial Bold Italic.ttf"),
    ("/System/Library/Fonts/Supplemental/Arial.ttf", "Arial Bold.ttf", "Arial Italic.ttf",
     "Arial Bold Italic.ttf"),
    ("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
    ("/usr/share/fonts/dejavu-sans-fonts/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
    ("/usr/share/fonts/dejavu/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
    ("/usr/share/fonts/TTF/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
]
_PRIV = 0xE000   # private-use range used to protect backslash-escaped characters
_GLYPHS = None   # set by _register_fonts(): characters the chosen font can draw


def _register_fonts():
    """Prefer Liberation Sans / Arial, then DejaVu Sans; else built-in Helvetica.
    Returns (regular, bold, unicode_ok)."""
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    global _GLYPHS
    for reg, b, i, bi in _FONT_CANDIDATES:
        reg = Path(reg)
        if reg.exists():
            try:
                pdfmetrics.registerFont(TTFont("AvSans", str(reg)))
                names = {"normal": "AvSans"}
                for key, fn, nm in (("bold", b, "AvSans-B"), ("italic", i, "AvSans-I"),
                                    ("boldItalic", bi, "AvSans-BI")):
                    f = reg.parent / fn
                    pdfmetrics.registerFont(TTFont(nm, str(f if f.exists() else reg)))
                    names[key] = nm
                pdfmetrics.registerFontFamily("AvSans", **names)
                _GLYPHS = pdfmetrics.getFont("AvSans").face.charToGlyph
                return "AvSans", "AvSans-B", True
            except Exception:
                pass
    _GLYPHS = None
    return "Helvetica", "Helvetica-Bold", False


def _pdf_inline(text, unicode_ok):
    """Markdown inline subset -> reportlab Paragraph markup ('  \\n' = line break)."""
    # protect backslash escapes (\*, \_, \), ...) so they aren't treated as markup
    text = re.sub(r"\\([\\*_`\[\]()#>+\-.!|])", lambda m: chr(_PRIV + ord(m.group(1))), text)
    text = text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    text = re.sub(r"`([^`]+)`", r'<font face="Courier">\1</font>', text)
    text = re.sub(r"\[([^\]]+)\]\(([^)\s]+)\)",
                  lambda m: f'<link href="{m.group(2).replace(chr(34), "")}" color="#1a5fb4">{m.group(1)}</link>',
                  text)
    text = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", text)
    text = re.sub(r"(?<!\*)\*(?!\s)(.+?)(?<!\s)\*(?!\*)", r"<i>\1</i>", text)
    text = re.sub(f"[{chr(_PRIV)}-{chr(_PRIV + 127)}]", lambda m: chr(ord(m.group(0)) - _PRIV), text)
    text = text.replace("  \n", "<br/>").replace("\n", " ")
    text = re.sub(r"^(\s*<br/>)+|(<br/>\s*)+$", "", text)     # no dangling line breaks
    if unicode_ok and _GLYPHS is not None:   # swap symbols the font can't draw (e.g. emoji)
        text = "".join(c if ord(c) < 128 or ord(c) in _GLYPHS else "*" for c in text)
    if not unicode_ok:   # built-in fonts only cover Latin-1/cp1252
        text = re.sub(r"[\u2606\u2605\u2B51\u2728]", "*", text)
        text = text.encode("cp1252", errors="replace").decode("cp1252")
    return text


def _xml(s, unicode_ok=True):
    return _pdf_inline(esc(s), unicode_ok)


def _load_image(path):
    """PIL image as RGB(A) -> (BytesIO, w, h). Full resolution; re-encoded so WebP etc. work."""
    import io
    from PIL import Image as PILImage
    with PILImage.open(path) as im:
        im.load()
        w, h = im.size
        buf = io.BytesIO()
        if im.mode in ("RGBA", "LA", "P"):
            im.convert("RGBA").save(buf, "PNG")
        else:
            im.convert("RGB").save(buf, "JPEG", quality=88)
    buf.seek(0)
    return buf, w, h


def _fit_image(path, max_w, max_h):
    from reportlab.platypus import Image
    buf, w, h = _load_image(path)
    scale = min(max_w / w, max_h / h, 1.0)
    return Image(buf, width=w * scale, height=h * scale)


def _palette(path):
    """Pick an accent hue from the pattern's cover photo (falls back to teal)."""
    import colorsys
    hue = 0.48
    try:
        from PIL import Image as PILImage
        with PILImage.open(path) as im:
            im = im.convert("RGB")
            im.thumbnail((96, 96))
            raw = im.tobytes()
            px = [tuple(raw[i:i + 3]) for i in range(0, len(raw), 3)]
        weights = [0.0] * 12
        for r, g, b in px:
            h, s, v = colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)
            if s > 0.3 and 0.25 < v < 0.95:
                weights[int(h * 12) % 12] += s * v
        if sum(weights) > 5:
            hue = (max(range(12), key=weights.__getitem__) + 0.5) / 12
    except Exception:
        pass
    from reportlab.lib.colors import Color
    mk = lambda s, v: Color(*colorsys.hsv_to_rgb(hue, s, v))
    return {"dark": mk(0.72, 0.36), "mid": mk(0.62, 0.58), "tint": mk(0.14, 0.97),
            "tint2": mk(0.06, 0.985), "bg": mk(0.30, 0.92), "dots": mk(0.16, 0.97)}


def render_pdf(d, base_dir, pdf_path):
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import letter
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.lib.units import inch
    from reportlab.lib.utils import ImageReader, simpleSplit
    from reportlab.platypus import (CondPageBreak, HRFlowable, PageBreak, Paragraph,
                                    SimpleDocTemplate, Spacer, Table, TableStyle)

    reg, bold, uni = _register_fonts()
    italic = {"AvSans-B": "AvSans-I"}.get(bold, "Helvetica-Oblique")
    px = lambda s: _pdf_inline(s, uni)               # markdown-inline -> markup
    title = d["title"]
    cover_paths = [base_dir / r for r in d["cover_imgs"] if (base_dir / r).exists()]
    pal = _palette(cover_paths[0]) if cover_paths else _palette(None)

    page_w, page_h = letter
    margin = 0.8 * inch
    fw = page_w - 2 * margin
    GREY = colors.HexColor("#777777")

    body = ParagraphStyle("body", fontName=reg, fontSize=10, leading=14.5)
    S = {
        "body": body,
        "cell": ParagraphStyle("cell", parent=body, leading=14),
        "label": ParagraphStyle("label", parent=body, fontName=bold, textColor=pal["dark"]),
        "h1": ParagraphStyle("h1", parent=body, fontName=bold, fontSize=19, leading=23,
                             textColor=pal["dark"], spaceBefore=12, spaceAfter=2),
        "band": ParagraphStyle("band", parent=body, fontName=bold, fontSize=13, leading=17,
                               textColor=colors.white),
        "sub": ParagraphStyle("sub", parent=body, fontName=bold, fontSize=11.5, leading=15,
                              textColor=pal["dark"], spaceBefore=8, spaceAfter=1),
        "cat": ParagraphStyle("cat", parent=body, fontName=bold, fontSize=9, leading=12,
                              textColor=GREY, spaceBefore=6, spaceAfter=2),
        "small": ParagraphStyle("small", parent=body, fontSize=8.5, leading=11.5, textColor=GREY),
        "note": ParagraphStyle("note", parent=body, fontName=italic),
    }

    def P(text, style="body"):
        return Paragraph(px(text), S[style])

    story = [PageBreak()]          # page 1 is the cover, drawn on the canvas

    def rule(thickness, color, after):
        r = HRFlowable(width="100%", thickness=thickness, color=color, spaceBefore=1, spaceAfter=after)
        return r

    def heading(text, level="h1"):
        story.append(CondPageBreak(1.7 * inch))
        story.append(Paragraph(_xml(text, uni), S[level]))
        if level == "h1":
            story.append(rule(1.6, pal["mid"], 7))

    def box(rows_or_flowables, accent_bar=True):
        t = Table([[f] for f in rows_or_flowables], colWidths=[fw])
        style = [("BACKGROUND", (0, 0), (-1, -1), pal["tint"]),
                 ("LEFTPADDING", (0, 0), (-1, -1), 12), ("RIGHTPADDING", (0, 0), (-1, -1), 10),
                 ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 3)]
        if accent_bar:
            style.append(("LINEBEFORE", (0, 0), (0, -1), 4, pal["mid"]))
        t.setStyle(TableStyle(style))
        return t

    total_imgs = (max(len(d["cover_imgs"]) - 1, 0)      # the first cover photo goes on the cover page
                  + (len(d["measure"]["imgs"]) if d["measure"] else 0)
                  + sum(1 for it in (d["items"] or []) if it["t"] == "image"))
    placed = [0]
    prep = Progress("preparing PDF photos", total_imgs) if total_imgs else None

    def photo_grid(rels, max_h=2.9 * inch):
        """Photos placed 2-up (a single photo is centred and a bit larger)."""
        paths = [base_dir / r for r in rels if (base_dir / r).exists()]
        if not paths:
            return
        n = len(paths)
        per_row = 1 if n == 1 else (3 if n >= 5 else 2)
        gap = 10
        cell_w = (fw - gap * (per_row - 1)) / per_row
        mh = {1: 3.2 * inch, 2: max_h, 3: 2.3 * inch}[per_row]
        cells = []
        for p in paths:
            try:
                cells.append(_fit_image(p, cell_w, mh))
                placed[0] += 1
                prep.update(placed[0])
            except Exception as e:
                print(f"     [warn] PDF: couldn't place {p.name}: {e}", file=sys.stderr)
        for i in range(0, len(cells), per_row):
            row = cells[i:i + per_row]
            t = Table([row], colWidths=[cell_w] * len(row), hAlign="CENTER")   # short last row is centred
            t.setStyle(TableStyle([("ALIGN", (0, 0), (-1, -1), "CENTER"),
                                   ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                                   ("LEFTPADDING", (0, 0), (-1, -1), 3), ("RIGHTPADDING", (0, 0), (-1, -1), 3),
                                   ("BOTTOMPADDING", (0, 0), (-1, -1), 6)]))
            story.append(t)
        story.append(Spacer(1, 4))

    # ---- at a glance + extra cover photos ----
    glance = []
    for k, v in d["info"]:
        glance.append(Table([[Paragraph(f"<b>{_xml(k, uni)}</b>", S["label"]), P(esc(v), "cell")]],
                            colWidths=[0.95 * inch, fw - 0.95 * inch - 22],
                            style=[("VALIGN", (0, 0), (-1, -1), "TOP"),
                                   ("LEFTPADDING", (0, 0), (-1, -1), 0),
                                   ("TOPPADDING", (0, 0), (-1, -1), 1),
                                   ("BOTTOMPADDING", (0, 0), (-1, -1), 1)]))
    if d["tags"]:
        glance.append(Paragraph(" ".join(_xml(t, uni) for t in d["tags"]), S["small"]))
    if glance:
        heading("At a glance")
        story += [box(glance), Spacer(1, 8)]
    if len(d["cover_imgs"]) > 1:
        photo_grid(d["cover_imgs"][1:])

    # ---- about / measurements ----
    if d["about"]:
        heading("About this pattern")
        for b in d["about"]:
            story += [P(b), Spacer(1, 5)]
    if d["measure"]:
        heading("Measurements")
        for b in d["measure"]["paras"]:
            story += [P(b), Spacer(1, 4)]
        photo_grid(d["measure"]["imgs"])

    # ---- materials ----
    if d["materials"]:
        heading("Materials")
        for g in d["materials"]:
            if g["cat"]:
                story.append(Paragraph(_xml(g["cat"].upper(), uni), S["cat"]))
            has_sw = any(it["hex"] for it in g["items"])
            spans = []
            rows, styles = [], [("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                                ("LINEBELOW", (0, 0), (-1, -1), 0.3, colors.HexColor("#dddddd")),
                                ("TOPPADDING", (0, 0), (-1, -1), 4), ("BOTTOMPADDING", (0, 0), (-1, -1), 4)]
            for r, it in enumerate(g["items"]):
                name = f"<b>{_xml(it['name'], uni)}</b>" if it["name"] else ""
                if it["weight"]:
                    name += f" <font color='#777777'>{_xml(it['weight'], uni)}</font>"
                text = "" if re.fullmatch(r"[.\u2026\s-]*", it["text"]) else px(it["text"])
                if it["link"]:
                    text += f" <link href='{it['link']}' color='#1a5fb4'>[link]</link>"
                row = []
                if has_sw:
                    row.append("")
                    if it["hex"]:
                        try:
                            styles.append(("BACKGROUND", (0, r), (0, r), colors.HexColor(it["hex"])))
                            styles.append(("LINEBELOW", (0, r), (0, r), 3, colors.white))
                        except Exception:
                            pass
                if name:
                    row += [Paragraph(name, S["cell"]), Paragraph(text, S["cell"])]
                else:                       # nothing to put in the name column: let the text span it
                    spans.append(("SPAN", (len(row), r), (len(row) + 1, r)))
                    row += [Paragraph(text, S["cell"]), ""]
                rows.append(row)
            widths = ([0.3 * inch] if has_sw else []) + [1.25 * inch]
            widths.append(fw - sum(widths))
            t = Table(rows, colWidths=widths)
            t.setStyle(TableStyle(styles + spans))
            story += [t, Spacer(1, 6)]

    # ---- abbreviations (compact, before the instructions - like a printed pattern) ----
    if d["abbr"]:
        heading("Abbreviations")
        pairs = [(Paragraph(f"<b>{_xml(a, uni)}</b>", S["label"]), Paragraph(_xml(b, uni), S["cell"]))
                 for a, b in d["abbr"]]
        rows = []
        for i in range(0, len(pairs), 2):
            chunk = pairs[i:i + 2]
            row = [chunk[0][0], chunk[0][1]] + ([chunk[1][0], chunk[1][1]] if len(chunk) > 1 else ["", ""])
            rows.append(row)
        aw = 0.65 * inch
        t = Table(rows, colWidths=[aw, fw / 2 - aw, aw, fw / 2 - aw])
        t.setStyle(TableStyle([("VALIGN", (0, 0), (-1, -1), "TOP"),
                               ("LINEBELOW", (0, 0), (-1, -1), 0.3, colors.HexColor("#dddddd")),
                               ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 3)]))
        story += [t, Spacer(1, 6)]

    # ---- instructions ----
    items = d["items"] or []
    if items:
        story.append(CondPageBreak(3 * inch))
        heading("Instructions")

    hexof = lambda c: "#%02x%02x%02x" % (int(c.red * 255), int(c.green * 255), int(c.blue * 255))
    acc = hexof(pal["mid"])

    def part_heading(text, big):
        """UPPERCASE accent heading; a trailing "(...)" is set lighter, e.g. HEAD (in mint yarn)."""
        m = re.match(r"^(.*?)\s*(\([^()]*\))\s*$", text)
        main, extra = (m.group(1), m.group(2)) if m and m.group(1) else (text, "")
        size = 16 if big else 12.5
        markup = f'<font name="{bold}" size="{size}" color="{acc}">{px(main.upper())}</font>'
        if extra:
            markup += f' <font name="{reg}" size="10" color="{acc}">{px(extra)}</font>'
        st = ParagraphStyle("part", parent=body, fontSize=size, leading=size + 5,
                            spaceBefore=12 if big else 8, spaceAfter=4)
        story.append(CondPageBreak(1.5 * inch))
        story.append(Paragraph(markup, st))

    S["rnd"] = ParagraphStyle("rnd", parent=body, spaceAfter=2.5)

    i = 0
    while i < len(items):
        it = items[i]
        t = it["t"]
        if t == "section":
            part_heading(it["text"], True)
        elif t == "sub":
            part_heading(it["text"], False)
        elif t == "text":
            story += [P(it["text"]), Spacer(1, 3)]
        elif t in ("round", "expanded") and not it.get("symbol"):
            label = it["label"] if t == "round" else "\u21b3"
            story.append(Paragraph(
                f'<font name="{bold}" color="{acc}">{_xml(label, uni)}:</font> {px(it["text"])}', S["rnd"]))
        elif t == "round":      # note bullet (star etc.) -> plain italic note
            story += [P(it["text"], "note"), Spacer(1, 3)]
        elif t == "image":
            rels = []
            while i < len(items) and items[i]["t"] == "image":     # group neighbouring photos
                rels.append(items[i]["rel"])
                i += 1
            photo_grid(rels)
            continue
        # markers (missing photo / video notes) are not shown in the PDF
        i += 1

    # ---- page furniture ----
    def draw_cover(c):
        c.setFillColor(pal["bg"])
        c.rect(0, 0, page_w, page_h, stroke=0, fill=1)
        c.setFillColor(pal["dots"])
        for yy in range(18, int(page_h), 44):
            for xx in range(18, int(page_w), 44):
                c.circle(xx, yy, 6, stroke=0, fill=1)
        tx = _pdf_inline(esc(title), uni)
        tx = re.sub(r"<[^>]+>", "", tx).replace("&amp;", "&").replace("&lt;", "<").replace("&gt;", ">")
        size = 38
        while size > 22:
            lines = simpleSplit(tx, bold, size, page_w - 2 * margin)
            if len(lines) <= 3:
                break
            size -= 3
        y = page_h - 0.95 * inch
        c.setFillColor(pal["dark"])
        c.setFont(bold, size)
        for ln in lines:
            c.drawCentredString(page_w / 2, y, ln)
            y -= size * 1.15
        if d["designer"]:
            y -= 2
            c.setFont(reg, 14)
            dsg = re.sub(r"<[^>]+>", "", _pdf_inline(esc(d["designer"]), uni)).replace("&amp;", "&")
            c.drawCentredString(page_w / 2, y, dsg)
            y -= 14
        pill = [f"{k}: {v}" for k, v in d["info"] if re.search(r"level|size", k, re.I) and v][:2]
        pill_h = (18 * len(pill) + 14) if pill else 0
        frame_top = y - 18
        frame_bottom = 0.9 * inch + (pill_h + 22 if pill else 0)
        if cover_paths and frame_top - frame_bottom > 2 * inch:
            fx, fwid, fh = 0.6 * inch, page_w - 1.2 * inch, frame_top - frame_bottom
            c.setFillColor(colors.white)
            c.setStrokeColor(pal["mid"])
            c.setLineWidth(5)
            c.roundRect(fx, frame_bottom, fwid, fh, 14, stroke=1, fill=1)
            try:
                buf, w, h = _load_image(cover_paths[0])
                pad = 14
                sc = min((fwid - 2 * pad) / w, (fh - 2 * pad) / h)
                iw, ih = w * sc, h * sc
                c.drawImage(ImageReader(buf), fx + (fwid - iw) / 2, frame_bottom + (fh - ih) / 2, iw, ih)
            except Exception as e:
                print(f"     [warn] PDF: couldn't place the cover photo: {e}", file=sys.stderr)
        if pill:
            wtxt = max(c.stringWidth(p, bold, 12.5) for p in pill) + 28
            c.setFillColor(pal["dark"])
            c.roundRect(0.6 * inch, 0.9 * inch, wtxt, pill_h, 7, stroke=0, fill=1)
            c.setFillColor(colors.white)
            c.setFont(bold, 12.5)
            for n, p in enumerate(pill):
                c.drawString(0.6 * inch + 14, 0.9 * inch + pill_h - 22 - 18 * n, p)

    def on_first(c, doc):
        _status("[info] writing PDF: page 1")
        c.saveState()
        draw_cover(c)
        c.restoreState()

    def on_later(c, doc):
        pages_done[0] = doc.page
        _status(f"[info] writing PDF: page {doc.page}")
        c.saveState()
        c.setStrokeColor(colors.HexColor("#dddddd"))
        c.setLineWidth(0.5)
        c.line(margin, 0.62 * inch, page_w - margin, 0.62 * inch)
        c.setFont(reg, 8)
        c.setFillColor(GREY)
        tt = re.sub(r"<[^>]+>", "", _pdf_inline(esc(title), uni)).replace("&amp;", "&")
        c.drawString(margin, 0.45 * inch, tt)
        c.drawRightString(page_w - margin, 0.45 * inch, str(doc.page))
        c.restoreState()

    if prep:
        prep.finish()
    t_write = time.monotonic()
    pages_done = [0]
    tmp_path = pdf_path.with_name(pdf_path.name + ".partial")
    doc = SimpleDocTemplate(str(tmp_path), pagesize=letter, leftMargin=margin, rightMargin=margin,
                            topMargin=0.75 * inch, bottomMargin=0.85 * inch, title=title,
                            author=d["designer"] or "")
    try:
        doc.build(story, onFirstPage=on_first, onLaterPages=on_later)
        os.replace(tmp_path, pdf_path)
        _status(f"[info] writing PDF: {doc.page} pages  [{_fmt_secs(time.monotonic() - t_write)}]", final=True)
    finally:
        if tmp_path.exists():
            tmp_path.unlink()
    return pdf_path



def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Convert a saved crochet pattern page into Markdown + PDF. "
                    "A <name>.json next to <name>.html supplies the step photos.")
    ap.add_argument("file", type=Path, help="the saved .html pattern page")
    ap.add_argument("-o", "--out", type=Path, default=Path("patterns"),
                    help="output folder (default: ./patterns)")
    ap.add_argument("--label", default="Rnd", metavar="WORD",
                    help='word in front of the round numbers: "Rnd" (default) or e.g. "Row"')
    ap.add_argument("--no-pdf", action="store_true", help="write only the Markdown")
    args = ap.parse_args(argv)

    if not args.file.exists():
        print(f"[FAIL] {args.file} not found", file=sys.stderr)
        return 1

    photo_urls, photo_title, referer = None, None, None
    photos_json = args.file.with_suffix(".json")
    if photos_json.exists():
        try:
            d = json.loads(photos_json.read_text(encoding="utf-8"))
            photo_title = d.get("title")
            referer = d.get("referer")
            photo_urls = {}
            for k, v in d["photos"].items():
                # local paths in the JSON are relative to the JSON file itself
                photo_urls[str(k)] = v if re.match(r"https?://", v) else str(photos_json.parent / v)
            print(f"[info] using {photos_json.name} ({len(photo_urls)} step photos)")
        except Exception as e:
            print(f"[FAIL] couldn't read {photos_json}: {e}", file=sys.stderr)
            return 1
    else:
        print(f"[info] no {photos_json.name} next to the page - step photos will be marked, not inserted")

    args.out.mkdir(parents=True, exist_ok=True)
    t_start = time.monotonic()
    print(f"[info] reading {args.file.name} ...", file=sys.stderr, flush=True)
    try:
        out_path, s, data = convert(args.file, args.out, photo_urls=photo_urls,
                                    photo_title=photo_title, referer=referer,
                                    label_word=args.label)
    except Exception as e:
        print(f"[FAIL] {args.file.name}: {e}", file=sys.stderr)
        return 1
    print(f"[ok] {out_path}  ({s['rows']} rows, {s['images']} images saved, "
          f"{s['photo_markers']} photo markers)")
    if s["photos_failed"]:
        src, err = s["first_error"]
        print(f"[warn] {s['photos_failed']} step photo(s) couldn't be downloaded and are marked "
              f"in the Markdown instead.\n       first failure: {src}\n       {err}", file=sys.stderr)
        if s["gave_up"]:
            print(f"       (stopped trying after {MAX_FAILURES_IN_A_ROW} failures in a row - "
                  f"check your connection and run it again)", file=sys.stderr)
    if s["mismatch"]:
        print(f"     note: {s['mismatch']} collapsed row(s) differed from their "
              f"expansions; the expansions were listed under them")
    if not args.no_pdf:
        try:
            pdf_path = render_pdf(data, args.out, out_path.with_suffix(".pdf"))
        except ImportError:
            print("[FAIL] the PDF needs reportlab:  pip install reportlab   "
                  "(the Markdown was still written; or use --no-pdf)", file=sys.stderr)
            return 1
        except Exception as e:
            print(f"[FAIL] couldn't write the PDF: {e}", file=sys.stderr)
            return 1
        print(f"[ok] {pdf_path}")
    print(f"[done] {_fmt_secs(time.monotonic() - t_start)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())

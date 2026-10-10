#!/usr/bin/env python3
"""
pat2md.py - turn crochet pattern web pages (saved with the SingleFile browser
extension) into plain-text Markdown files + a folder of extracted images.

Usage
-----
    pip install beautifulsoup4 lxml
    python pat2md.py "Vulpes the fox.html" -o patterns/
    python pat2md.py "Vulpes the fox.html" -o patterns/ --photos "Vulpes the fox.json"

One page per run. Output layout:

    patterns/
        vulpes-the-fox.md
        images/
            vulpes-the-fox/cover-01.jpg
            vulpes-the-fox/measurements-01.jpg
            vulpes-the-fox/step-01.png
            ...

The Markdown never contains base64 data: images are written to disk and
referenced as ![alt](images/<pattern>/<file>) at the spot where they appeared.

What is (and isn't) in the saved HTML
-------------------------------------
Embedded in the file, so extracted:  cover photos, measurement photos, and any
step photo that was expanded on the page when you saved it.
NOT in the file: the per-step photos behind the little camera icons. Those are
fetched from the site's server only when you click the icon, so the saved page
never contains them. Where one existed, the Markdown gets a short text marker
(--no-photo-markers leaves those out). To get the photos, collect their URLs
with the browser-console snippet and pass the resulting JSON with --photos.

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
import re
import sys
import urllib.request
from pathlib import Path

from bs4 import BeautifulSoup, NavigableString, Tag

try:  # lxml is faster and more forgiving; fall back to the stdlib parser
    import lxml  # noqa: F401
    PARSER = "lxml"
except ImportError:  # pragma: no cover
    PARSER = "html.parser"

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
        """Get a step photo from a URL or a local file path (see --photos).
        Returns the relative path, or None on failure."""
        try:
            if re.match(r"https?://", src):
                headers = {"User-Agent": "Mozilla/5.0"}
                if self.referer:
                    headers["Referer"] = self.referer
                req = urllib.request.Request(src, headers=headers)
                with urllib.request.urlopen(req, timeout=30) as r:
                    data = r.read()
                    ctype = r.headers.get("Content-Type", "").split(";")[0].strip().lower()
                ext = MIME_EXT.get(ctype) or Path(src.split("?")[0]).suffix.lower() or ".png"
            else:
                path = Path(src)
                data, ext = path.read_bytes(), path.suffix.lower() or ".png"
        except Exception as e:
            print(f"     [warn] couldn't get step photo {src}: {e}", file=sys.stderr)
            return None
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
    """-> list of (category or None, [item markdown lines])"""
    ul = container.select_one("ul.mat-table")
    if not ul:
        return []
    groups, current = [], None
    for ch in ul.find_all(recursive=False):
        if ch.name == "span" and ch.find("h2"):
            current = (plain(ch.find("h2")), [])
            groups.append(current)
        elif ch.name == "li" and "mat-line" in (ch.get("class") or []):
            if current is None:
                current = (None, [])
                groups.append(current)
            name = plain(ch.select_one(".colorpicker-name"))
            swatch = ch.select_one(".colorpicker-swatch")
            m = re.search(r"#[0-9a-fA-F]{3,8}", (swatch.get("style") or "") if swatch else "")
            item = ch.select_one(".mat_item")
            weight = plain(item.select_one(".mat_weight")) if item else ""
            text = ""
            if item:
                clone = BeautifulSoup(str(item), PARSER)
                for w in clone.select(".mat_weight, .mat_link, .mat-link-icon-inline"):
                    w.decompose()
                text = tidy(inline(clone))
            link = item.select_one("[data-full_link]") if item else None
            line = "- "
            if name:
                line += f"**{esc(name)}**: "
            if weight:
                line += f"({esc(weight)}) "
            line += text
            if m:
                line += f" - colour `{m.group(0)}`"
            if link and link.get("data-full_link"):
                line += f" ([link]({link['data-full_link']}))"
            current[1].append(line.rstrip())
    return [g for g in groups if g[1]]


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


def instructions(ul, images, markers=True, photo_urls=None):
    """Walk <ul id=ul_main> in document order and emit Markdown blocks.
    Returns (lines, stats)."""
    photo_urls = photo_urls or {}
    out = []                       # list of (kind, text)
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
            out.append(("h", f"### {text}"))
        elif cls == "SubSectionRow":
            out.append(("h", f"#### {text}"))
        elif cls == "RndRow":
            if re.search(r"[0-9A-Za-z]", label):
                # drop a leading "3)" / "4)-5)" if it just repeats the label
                m = re.match(r"^\s*(\d+)\\?\)(?:\s*-\s*\d+\\?\))?\s*", text)
                n = re.match(r"\d+", label)
                if m and n and m.group(1) == n.group(0):
                    text = text[m.end():]
                lab = label.replace("-", "\u2013") if re.fullmatch(r"\d+-\d+", label) else label
                out.append(("r", f"- **{esc(lab)}:** " + text.replace("\n", "\n  ")))
            else:  # symbol-style note marker such as a star
                out.append(("r", f"- {label} {text}".rstrip()))
        else:  # TextRow
            out.append(("t", text))

        rid = (li.get("id") or "")
        line_no = rid[2:] if rid.startswith("li") else None
        fetched = False
        if line_no in photo_urls and line_no not in embedded_after:
            rel = images.download(photo_urls[line_no])
            if rel:
                out.append(("i", f"![step photo]({rel})"))
                stats["photos_saved"] += 1
                fetched = True
        if not markers:
            return
        indent = "  " if out[-1][0] == "r" else ""
        kind = "m" if indent else "p"
        if has_icon(li, "Click to see video"):
            out.append((kind, indent + VIDEO_MARKER))
            stats["photo_markers"] += 1
        if (not fetched and line_no not in embedded_after
                and has_icon(li, "Click to see photo")):
            out.append((kind, indent + PHOTO_MARKER))
            stats["photo_markers"] += 1

    for ch in ul.find_all(recursive=False):
        if ch.name == "li" and ch.get("data-ext") == "img":
            img = ch.find("img")
            rel = images.save(img, "step") if img else None
            if rel:
                out.append(("i", f"![step photo]({rel})"))
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
                        out.append(("w", f"  - *(expanded row {plain(inner.select_one('td.t2'))}):* {inline_clean(t3)}"))

    # join with sensible blank lines (consecutive list rows stay tight)
    lines, prev = [], None
    for kind, text in out:
        if prev is not None:
            tight = (prev in ("r", "m", "w") and kind in ("r", "m", "w"))
            lines.append("" if not tight else None)
        lines.append(text)
        prev = kind
    return [ln for ln in lines if ln is not None], stats


# --------------------------------------------------------------------------
# one pattern file -> markdown
# --------------------------------------------------------------------------
def convert(path, out_dir, markers=True, photo_urls=None, photo_title=None, referer=None):
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
    if photo_title and slugify(photo_title) != slug:
        print(f"[warn] the photos JSON is for '{photo_title}' but this page is "
              f"'{title}' - double-check you paired the right files", file=sys.stderr)

    cover = page.select_one(".wrapper-cover")
    designer = plain(page.select_one("#designer-cover"))

    md = [f"# {esc(title)}", ""]
    if designer:
        md += [f"*{esc(designer)}*", ""]

    # ---- cover photos
    cover_imgs = []
    for img in cover.select(".pattern_image_cover img"):
        rel = images.save(img, "cover")
        if rel and rel not in cover_imgs:
            cover_imgs.append(rel)
    for i, rel in enumerate(cover_imgs, 1):
        md += [f"![{esc(title)} - cover photo {i}]({rel})", ""]

    # ---- quick facts
    info, tags = cover_info(cover)
    if info:
        md += [f"- **{esc(k)}:** {esc(v)}" for k, v in info]
        md.append("")
    if tags:
        md += ["Tags: " + " ".join(esc(t) for t in tags), ""]

    # ---- about
    about = page.select_one(".abbr-container .abbr-intro")
    if about and plain(about):
        md += ["## About this pattern", ""]
        for b in blocks(about):
            md += [b, ""]

    # ---- measurements
    meas = page.select_one(".measure_text")
    abbr_rows = []
    if meas:
        intro = meas.select_one(".abbr-intro")
        meas_imgs = []
        for img in meas.select("#measure_img_mobile img"):
            rel = images.save(img, "measurements")
            if rel and rel not in meas_imgs:
                meas_imgs.append(rel)
        if (intro and plain(intro)) or meas_imgs:
            md += ["## Measurements", ""]
            if intro:
                for b in blocks(intro):
                    md += [b, ""]
            for i, rel in enumerate(meas_imgs, 1):
                md += [f"![measurements photo {i}]({rel})", ""]
        abbr_rows = abbreviations(meas)

    # ---- materials
    mat = page.select_one(".materials_page_container")
    if mat:
        groups = materials(mat)
        if groups:
            md += ["## Materials", ""]
            for cat, items in groups:
                if cat:
                    md += [f"### {esc(cat)}", ""]
                md += items + [""]

    # ---- instructions
    ul = page.find(id="ul_main")
    stats = {"rows": 0, "photos_saved": 0, "photo_markers": 0, "mismatch": 0}
    if ul:
        md += ["## Instructions", ""]
        body, stats = instructions(ul, images, markers, photo_urls)
        md += body + [""]

    # ---- abbreviations
    if abbr_rows:
        md += ["## Abbreviations", "", "| Abbreviation | Meaning |", "| --- | --- |"]

        def cell(s):
            return esc(s).replace("|", "\\|")
        md += [f"| {cell(a)} | {cell(b)} |" for a, b in abbr_rows]
        md.append("")

    text = "\n".join(md)
    text = re.sub(r"\n{3,}", "\n\n", text).rstrip() + "\n"
    out_path = out_dir / f"{slug}.md"
    out_path.write_text(text, encoding="utf-8")

    stats["images"] = len(images.seen)
    return out_path, stats


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Convert ONE crochet pattern page saved with SingleFile into Markdown.")
    ap.add_argument("file", type=Path, help="the saved .html pattern page")
    ap.add_argument("-o", "--out", type=Path, default=Path("patterns"),
                    help="output folder (default: ./patterns)")
    ap.add_argument("--photos", type=Path, metavar="JSON",
                    help="photos JSON made by the browser-console snippet (default: "
                         "<page>.photos.json next to the HTML file, if it exists)")
    ap.add_argument("--no-photos", action="store_true",
                    help="ignore any <page>.photos.json")
    ap.add_argument("--no-photo-markers", action="store_true",
                    help="don't insert a text note where a (non-saved) step photo/video existed")
    args = ap.parse_args(argv)

    photo_urls, photo_title, referer = None, None, None
    photos_json = args.photos
    if not photos_json and not args.no_photos:
        auto = args.file.with_suffix(".photos.json")
        if auto.exists():
            photos_json = auto
            print(f"[info] using {auto.name}")
    if photos_json:
        try:
            d = json.loads(photos_json.read_text(encoding="utf-8"))
            photo_title = d.get("title")
            referer = d.get("referer")
            photo_urls = {}
            for k, v in d["photos"].items():
                # local paths in the JSON are relative to the JSON file itself
                photo_urls[str(k)] = v if re.match(r"https?://", v) else str(photos_json.parent / v)
        except Exception as e:
            print(f"[FAIL] couldn't read {photos_json}: {e}", file=sys.stderr)
            return 1

    args.out.mkdir(parents=True, exist_ok=True)
    try:
        out_path, s = convert(args.file, args.out, markers=not args.no_photo_markers,
                              photo_urls=photo_urls, photo_title=photo_title, referer=referer)
    except Exception as e:
        print(f"[FAIL] {args.file.name}: {e}", file=sys.stderr)
        return 1
    print(f"[ok] {out_path}  ({s['rows']} rows, {s['images']} images saved, "
          f"{s['photo_markers']} photo markers)")
    if s["mismatch"]:
        print(f"     note: {s['mismatch']} collapsed row(s) differed from their "
              f"expansions; the expansions were listed under them")
    return 0


if __name__ == "__main__":
    sys.exit(main())

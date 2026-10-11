#!/usr/bin/env python3
"""
pat2md.py - turn crochet pattern web pages (saved with the SingleFile browser
extension) into plain-text Markdown files + a folder of extracted images.

Usage
-----
    pip install beautifulsoup4 lxml          # core
    pip install reportlab                    # only needed for --pdf
    python pat2md.py "Vulpes the fox.html" -o patterns/
    python pat2md.py "Vulpes the fox.html" -o patterns/ --photos "Vulpes the fox.json"
    python pat2md.py "Vulpes the fox.html" -o patterns/ --pdf     # also writes vulpes-the-fox.pdf

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


# --------------------------------------------------------------------------
# PDF output (--pdf): rendered from the Markdown this script just wrote
# --------------------------------------------------------------------------
_FONT_CANDIDATES = [   # (regular, bold, italic, bold-italic) - first set that exists wins
    ("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
    ("/usr/share/fonts/dejavu-sans-fonts/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
    ("/usr/share/fonts/dejavu/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
    ("/usr/share/fonts/TTF/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
    ("/Library/Fonts/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
    ("C:/Windows/Fonts/DejaVuSans.ttf", "DejaVuSans-Bold.ttf",
     "DejaVuSans-Oblique.ttf", "DejaVuSans-BoldOblique.ttf"),
]
_PRIV = 0xE000   # private-use range used to protect backslash-escaped characters
_GLYPHS = None   # set by _register_fonts(): characters the chosen font can draw


def _register_fonts():
    """Use DejaVu Sans if installed (covers symbols like the star bullets);
    otherwise fall back to built-in Helvetica. Returns (family, unicode_ok)."""
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    for reg, b, i, bi in _FONT_CANDIDATES:
        reg = Path(reg)
        if reg.exists():
            d = reg.parent
            try:
                pdfmetrics.registerFont(TTFont("PatSans", str(reg)))
                names = {"normal": "PatSans"}
                for key, fn, nm in (("bold", b, "PatSans-B"), ("italic", i, "PatSans-I"),
                                    ("boldItalic", bi, "PatSans-BI")):
                    f = d / fn
                    pdfmetrics.registerFont(TTFont(nm, str(f if f.exists() else reg)))
                    names[key] = nm
                pdfmetrics.registerFontFamily("PatSans", **names)
                global _GLYPHS
                _GLYPHS = pdfmetrics.getFont("PatSans").face.charToGlyph
                return "PatSans", True
            except Exception:
                pass
    return "Helvetica", False


def _pdf_inline(text, unicode_ok):
    """Markdown inline subset -> reportlab Paragraph markup."""
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
    if unicode_ok and _GLYPHS is not None:   # swap symbols the font can't draw (e.g. emoji)
        text = "".join(c if ord(c) < 128 or ord(c) in _GLYPHS else "*" for c in text)
    if not unicode_ok:   # built-in fonts only cover Latin-1/cp1252
        text = re.sub(r"[\u2606\u2605\u2B51\u2728]", "*", text)
        text = text.encode("cp1252", errors="replace").decode("cp1252")
    return text


def _pdf_image(path, max_w, max_h):
    """reportlab Image scaled to fit; re-encodes via Pillow so WebP etc. work."""
    import io
    from PIL import Image as PILImage
    from reportlab.platypus import Image
    with PILImage.open(path) as im:
        im.load()
        w, h = im.size
        buf = io.BytesIO()
        if im.mode in ("RGBA", "LA", "P"):
            im.convert("RGBA").save(buf, "PNG")
        else:
            im.convert("RGB").save(buf, "JPEG", quality=88)
    buf.seek(0)
    scale = min(max_w / w, max_h / h, 1.0)
    return Image(buf, width=w * scale, height=h * scale)


def write_pdf(md_text, base_dir, pdf_path):
    from reportlab.lib import colors
    from reportlab.lib.enums import TA_LEFT
    from reportlab.lib.pagesizes import letter
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.lib.units import inch
    from reportlab.platypus import (Paragraph, SimpleDocTemplate, Spacer, Table,
                                    TableStyle)

    family, uni = _register_fonts()
    bold = {"PatSans": "PatSans-B"}.get(family, "Helvetica-Bold")
    base = ParagraphStyle("base", fontName=family, fontSize=10, leading=14, alignment=TA_LEFT)
    st = {
        "p": base,
        "title": ParagraphStyle("title", parent=base, fontName=bold, fontSize=22, leading=27, spaceAfter=4),
        "h2": ParagraphStyle("h2", parent=base, fontName=bold, fontSize=15, leading=19,
                             spaceBefore=14, spaceAfter=6, keepWithNext=1),
        "h3": ParagraphStyle("h3", parent=base, fontName=bold, fontSize=12.5, leading=16,
                             spaceBefore=10, spaceAfter=4, keepWithNext=1),
        "h4": ParagraphStyle("h4", parent=base, fontName=bold, fontSize=11, leading=14,
                             spaceBefore=8, spaceAfter=3, keepWithNext=1, textColor=colors.HexColor("#444444")),
        "li": ParagraphStyle("li", parent=base, leftIndent=16, bulletIndent=4, spaceAfter=2),
    }
    margin = 0.8 * inch
    page_w, page_h = letter
    frame_w = page_w - 2 * margin

    story, para, bullet = [], [], None

    def flush_para():
        nonlocal para
        if para:
            story.append(Paragraph("".join(para), st["p"]))
            story.append(Spacer(1, 4))
        para = []

    def flush_bullet():
        nonlocal bullet
        if bullet is not None:
            story.append(Paragraph(bullet, st["li"], bulletText="\u2022" if uni else "-"))
        bullet = None

    def fmt(line):
        """one markdown line -> markup, honouring the trailing two-space hard break"""
        hard = line.endswith("  ")
        return _pdf_inline(line.strip(), uni) + ("<br/>" if hard else " ")

    lines = md_text.split("\n")
    i = 0
    while i < len(lines):
        ln = lines[i]
        i += 1
        if not ln.strip():
            flush_para(); flush_bullet(); continue

        m = re.match(r"^(#{1,4}) (.*)", ln)
        if m:
            flush_para(); flush_bullet()
            story.append(Paragraph(_pdf_inline(m.group(2), uni), st[("title", "h2", "h3", "h4")[len(m.group(1)) - 1]]))
            continue

        m = re.match(r"^!\[([^\]]*)\]\(([^)]+)\)\s*$", ln)
        if m:
            flush_para(); flush_bullet()
            img_path = base_dir / m.group(2)
            if img_path.exists():
                try:
                    story.append(_pdf_image(img_path, frame_w, 3.4 * inch))
                    story.append(Spacer(1, 6))
                except Exception as e:
                    print(f"     [warn] PDF: couldn't place {m.group(2)}: {e}", file=sys.stderr)
            continue

        if ln.startswith("|"):
            flush_para(); flush_bullet()
            rows = []
            i -= 1
            while i < len(lines) and lines[i].startswith("|"):
                if not re.match(r"^\|\s*-+", lines[i]):
                    cells = [c.strip() for c in re.split(r"(?<!\\)\|", lines[i].strip().strip("|"))]
                    rows.append(cells)
                i += 1
            if rows:
                data = [[Paragraph(("<b>%s</b>" if r == 0 else "%s") % _pdf_inline(c, uni), base)
                         for c in row] for r, row in enumerate(rows)]
                t = Table(data, colWidths=[1.3 * inch, frame_w - 1.3 * inch], repeatRows=1)
                t.setStyle(TableStyle([("GRID", (0, 0), (-1, -1), 0.4, colors.HexColor("#bbbbbb")),
                                       ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#eeeeee")),
                                       ("VALIGN", (0, 0), (-1, -1), "TOP")]))
                story.append(t)
                story.append(Spacer(1, 6))
            continue

        m = re.match(r"^- (.*)", ln)
        if m:
            flush_para(); flush_bullet()
            bullet = fmt(m.group(1))
            continue

        if bullet is not None and ln.startswith("  "):   # continuation of a list item
            bullet += fmt(ln)
            continue

        flush_bullet()
        para.append(fmt(ln))     # plain paragraph line
    flush_para(); flush_bullet()

    title = next((l[2:] for l in lines if l.startswith("# ")), "pattern")

    def footer(canvas, doc):
        canvas.saveState()
        canvas.setFont(family, 8)
        canvas.setFillColor(colors.HexColor("#777777"))
        canvas.drawCentredString(page_w / 2, 0.45 * inch, f"{doc.page}")
        canvas.restoreState()

    doc = SimpleDocTemplate(str(pdf_path), pagesize=letter, leftMargin=margin, rightMargin=margin,
                            topMargin=margin, bottomMargin=0.8 * inch,
                            title=re.sub(r"\\(.)", r"\1", title))
    doc.build(story, onFirstPage=footer, onLaterPages=footer)
    return pdf_path


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
    ap.add_argument("--pdf", action="store_true",
                    help="also write a PDF next to the Markdown file (needs: pip install reportlab)")
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
    if args.pdf:
        try:
            pdf_path = write_pdf(out_path.read_text(encoding="utf-8"), args.out,
                                 out_path.with_suffix(".pdf"))
        except ImportError:
            print("[FAIL] --pdf needs reportlab:  pip install reportlab", file=sys.stderr)
            return 1
        except Exception as e:
            print(f"[FAIL] couldn't write the PDF: {e}", file=sys.stderr)
            return 1
        print(f"[ok] {pdf_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

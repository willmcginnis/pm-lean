#!/usr/bin/env python3
"""Check written SVG files independently of the code that drew them.

    python3 check_svg.py FILE.svg ...

For each file: well-formed XML; a prefers-color-scheme: dark block; no
scripts, foreign objects or external references; every <text> inside the
image; and no two <text> elements overlapping, using a uniform, generous
width estimate (0.62 em per character, 0.68 em in bold; 1.0 em for wide
symbols) that is deliberately different from the drawing code's.
"""

import sys
import xml.dom.minidom

WIDE = set("✱⟷⊢≡—→")


def width(s, size, bold):
    em = 0.68 if bold else 0.62
    return sum(1.0 if c in WIDE else em for c in s) * size


def check(path):
    errs = []
    with open(path, encoding="utf-8") as f:
        raw = f.read()
    try:
        doc = xml.dom.minidom.parseString(raw.encode("utf-8"))
    except Exception as e:  # noqa: BLE001 - report any parse failure
        return [f"not well-formed XML: {e}"]
    root = doc.documentElement
    if "prefers-color-scheme: dark" not in raw:
        errs.append("no dark-mode block")
    for bad in ("script", "foreignObject", "image"):
        if doc.getElementsByTagName(bad):
            errs.append(f"contains <{bad}>")
    if "href=\"http" in raw or "url(http" in raw:
        errs.append("external reference")
    W, H = float(root.getAttribute("width")), float(root.getAttribute("height"))
    boxes = []
    for t in doc.getElementsByTagName("text"):
        s = "".join(n.data for n in t.childNodes if n.nodeType == n.TEXT_NODE)
        x, y = float(t.getAttribute("x")), float(t.getAttribute("y"))
        size = float(t.getAttribute("font-size"))
        bold = t.getAttribute("font-weight") in ("bold", "700")
        w = width(s, size, bold)
        anchor = t.getAttribute("text-anchor") or "start"
        x0 = x if anchor == "start" else (x - w / 2 if anchor == "middle" else x - w)
        b = (x0, y - 0.78 * size, x0 + w, y + 0.22 * size, s)
        if b[0] < 0 or b[1] < 0 or b[2] > W or b[3] > H:
            errs.append(f"text outside the image: {s!r}")
        boxes.append(b)
    boxes.sort()
    for i, a in enumerate(boxes):
        for b in boxes[i + 1:]:
            if b[0] >= a[2]:
                break
            if a[1] < b[3] and b[1] < a[3]:
                errs.append(f"overlap: {a[4]!r} / {b[4]!r}")
    return errs, len(boxes), (W, H)


def main():
    bad = 0
    for path in sys.argv[1:]:
        res = check(path)
        if isinstance(res, list):
            errs, n, size = res, 0, None
        else:
            errs, n, size = res
        if errs:
            bad += 1
            print(f"FAIL {path}")
            for e in errs:
                print(f"  {e}")
        else:
            print(f"ok   {path}: {size[0]:.0f}x{size[1]:.0f}, {n} texts, well-formed, dark mode, no overlaps")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()

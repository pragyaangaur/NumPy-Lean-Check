"""Draw the README figures from the repository itself.

It writes a light and a dark version of two SVG files into docs/images: the method as a pipeline, and the bug records by area and upstream verdict. The counts come from the bug records, so rerun this after scripts/findings.py whenever a record changes.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from findings import ROOT, VERDICTS, read_record, verdict  # noqa: E402
import glob  # noqa: E402

OUT = os.path.join(ROOT, "docs", "images")

THEMES = {
    "light": {
        "surface": "#fcfcfb", "panel": "#f1f0ec", "border": "#d8d6cf", "text": "#0b0b0b", "muted": "#52514e", "grid": "#e4e2dc",
        "series": ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4"], "accent": "#2a78d6",
        # Fills below 3:1 against white get dark labels instead.
        "ink": ["#ffffff", "#ffffff", "#0b0b0b", "#0b0b0b", "#0b0b0b"],
    },
    "dark": {
        "surface": "#1a1a19", "panel": "#252523", "border": "#3d3c39", "text": "#f0efec", "muted": "#c3c2b7", "grid": "#33322f",
        "series": ["#3987e5", "#d95926", "#199e70", "#c98500", "#d55181"], "accent": "#3987e5",
        "ink": ["#ffffff"] * 5,
    },
}
FONT = "-apple-system, BlinkMacSystemFont, 'Segoe UI', Helvetica, Arial, sans-serif"
MONO = "ui-monospace, SFMono-Regular, Menlo, Consolas, monospace"
LABELS = {"NEW": "New", "RELATED": "Related", "KNOWN-OPEN": "Known, open", "KNOWN-CLOSED": "Known, closed", "FIXED-ON-MAIN": "Fixed on main"}


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def pipeline(t):
    steps = [
        ("1", "Read the C", "NumPy 2.5.4 source,", "pinned to one commit"),
        ("2", "Mirror it in Lean", "same branches, same order,", "same overflow points"),
        ("3", "Race them", "50,000 inputs on 3 seeds", "must match NumPy exactly"),
        ("4", "Prove or refute", "a claim about every input,", "or find a counterexample"),
        ("5", "File the bug", "a record, a reproducer", "and a tracker search"),
    ]
    w, h, bw, bh, gap, top = 980, 210, 172, 120, 18, 46
    x0 = (w - (5 * bw + 4 * gap)) / 2
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}" width="{w}" height="{h}" role="img" aria-label="The method in five steps: read the C source, mirror it in Lean, race the model against NumPy, prove or refute properties, file the bug">',
         f'<rect width="{w}" height="{h}" rx="12" fill="{t["surface"]}"/>',
         f'<text x="{w/2}" y="28" text-anchor="middle" font-family="{FONT}" font-size="15" font-weight="600" fill="{t["muted"]}">How a bug is found</text>']
    for i, (num, head, l1, l2) in enumerate(steps):
        x = x0 + i * (bw + gap)
        o.append(f'<rect x="{x}" y="{top}" width="{bw}" height="{bh}" rx="10" fill="{t["panel"]}" stroke="{t["border"]}"/>')
        o.append(f'<circle cx="{x + 26}" cy="{top + 28}" r="14" fill="{t["accent"]}"/>')
        o.append(f'<text x="{x + 26}" y="{top + 33}" text-anchor="middle" font-family="{FONT}" font-size="14" font-weight="700" fill="#ffffff">{num}</text>')
        o.append(f'<text x="{x + 48}" y="{top + 33}" font-family="{FONT}" font-size="14.5" font-weight="700" fill="{t["text"]}">{esc(head)}</text>')
        o.append(f'<text x="{x + 14}" y="{top + 72}" font-family="{FONT}" font-size="12" fill="{t["muted"]}">{esc(l1)}</text>')
        o.append(f'<text x="{x + 14}" y="{top + 92}" font-family="{FONT}" font-size="12" fill="{t["muted"]}">{esc(l2)}</text>')
        if i < 4:
            ax = x + bw + 4
            o.append(f'<path d="M{ax} {top + bh/2} h{gap - 12} m-7 -6 l7 6 l-7 6" fill="none" stroke="{t["muted"]}" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>')
    o.append(f'<text x="{w/2}" y="{top + bh + 28}" text-anchor="middle" font-family="{FONT}" font-size="12.5" fill="{t["muted"]}">A mismatch in step 3 means the model is wrong and gets fixed. A refuted claim in step 4 that the real NumPy also shows is a bug.</text>')
    o.append("</svg>")
    return "\n".join(o)


def findings_chart(t, recs):
    areas = sorted({r["area"] for r in recs}, key=lambda a: (-sum(r["area"] == a for r in recs), a))
    order = [v for v in VERDICTS if v in LABELS]
    w, left, right, top, row, bar = 980, 120, 60, 92, 34, 20
    h = top + row * len(areas) + 40
    maxn = max(sum(r["area"] == a for r in recs) for a in areas)
    scale = (w - left - right) / maxn
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}" width="{w}" height="{h}" role="img" aria-label="Bug records by area, split by whether NumPy already knew about them">',
         f'<rect width="{w}" height="{h}" rx="12" fill="{t["surface"]}"/>',
         f'<text x="24" y="32" font-family="{FONT}" font-size="16" font-weight="700" fill="{t["text"]}">{len(recs)} bug records by area, and whether NumPy already knew</text>']
    lx = 24
    for i, v in enumerate(order):
        n = sum(r["verdict"] == v for r in recs)
        label = f"{LABELS[v]} ({n})"
        o.append(f'<rect x="{lx}" y="50" width="12" height="12" rx="3" fill="{t["series"][i]}"/>')
        o.append(f'<text x="{lx + 18}" y="60.5" font-family="{FONT}" font-size="12.5" fill="{t["muted"]}">{esc(label)}</text>')
        lx += 30 + len(label) * 7.1
    for k in range(0, maxn + 1, 2):
        gx = left + k * scale
        o.append(f'<line x1="{gx}" y1="{top - 8}" x2="{gx}" y2="{top + row * len(areas) - 8}" stroke="{t["grid"]}" stroke-width="1"/>')
        o.append(f'<text x="{gx}" y="{top + row * len(areas) + 8}" text-anchor="middle" font-family="{FONT}" font-size="11" fill="{t["muted"]}">{k}</text>')
    for j, a in enumerate(areas):
        y = top + j * row
        o.append(f'<text x="{left - 12}" y="{y + bar/2 + 4.5}" text-anchor="end" font-family="{FONT}" font-size="13" fill="{t["text"]}">{a}</text>')
        x = left
        total = 0
        for i, v in enumerate(order):
            n = sum(r["area"] == a and r["verdict"] == v for r in recs)
            if not n:
                continue
            segw = n * scale - 2
            o.append(f'<rect x="{x}" y="{y}" width="{segw}" height="{bar}" rx="4" fill="{t["series"][i]}"><title>{a}: {n} {LABELS[v].lower()}</title></rect>')
            if segw >= 16:
                o.append(f'<text x="{x + segw/2}" y="{y + bar/2 + 4.5}" text-anchor="middle" font-family="{FONT}" font-size="12" font-weight="600" fill="{t["ink"][i]}">{n}</text>')
            x += n * scale
            total += n
        o.append(f'<text x="{x + 6}" y="{y + bar/2 + 4.5}" font-family="{FONT}" font-size="12.5" font-weight="600" fill="{t["muted"]}">{total}</text>')
    o.append("</svg>")
    return "\n".join(o)


def main():
    os.makedirs(OUT, exist_ok=True)
    recs = [read_record(p) for p in sorted(glob.glob(os.path.join(ROOT, "bugs", "*.yaml")))]
    for r in recs:
        r["verdict"] = verdict(r)
    for mode, t in THEMES.items():
        open(os.path.join(OUT, f"pipeline-{mode}.svg"), "w").write(pipeline(t) + "\n")
        open(os.path.join(OUT, f"findings-{mode}.svg"), "w").write(findings_chart(t, recs) + "\n")
    print(f"wrote 4 figures from {len(recs)} records")


if __name__ == "__main__":
    main()

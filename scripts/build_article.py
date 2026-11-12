"""Build docs/index.html, the article page, from docs/article.md.

The Markdown is rendered by GitHub's own renderer through the gh command line tool, so the page shows the same code blocks and links as the repository does. GitHub Pages serves the docs folder at pragyaangaur.dev/NumPy-Lean-Check/.
"""
import html
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOCS = os.path.join(ROOT, "docs")
URL = "https://pragyaangaur.dev/NumPy-Lean-Check/"
FONTS = "https://pragyaangaur.dev/assets/fonts/"

CSS = """
@font-face { font-family: "Latin Modern"; font-weight: 400; font-display: swap; src: url("FONTS/LM-regular.woff2") format("woff2"); }
@font-face { font-family: "Latin Modern"; font-style: italic; font-weight: 400; font-display: swap; src: url("FONTS/LM-italic.woff2") format("woff2"); }
@font-face { font-family: "Latin Modern"; font-weight: 700; font-display: swap; src: url("FONTS/LM-bold.woff2") format("woff2"); }
:root { --bg: #fcfcfa; --ink: #1b1b1a; --muted: #5b5a56; --rule: #e2e0da; --code: #f2f1ec; --link: #1f5fbf; }
@media (prefers-color-scheme: dark) { :root { --bg: #181817; --ink: #ecebe6; --muted: #b3b1a8; --rule: #33322f; --code: #242422; --link: #7fb0f5; } }
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink); font: 20px/1.6 "Latin Modern", Georgia, serif; }
main { max-width: 860px; margin: 0 auto; padding: 56px 22px 80px; }
h1 { font-size: 2.05em; line-height: 1.2; margin: 0 0 12px; }
h2 { font-size: 1.3em; margin: 2em 0 0.5em; }
p, li { margin: 0 0 1em; }
li { margin-bottom: 0.45em; }
a { color: var(--link); text-decoration-thickness: 1px; text-underline-offset: 3px; }
em { color: var(--muted); }
code { font: 0.8em ui-monospace, SFMono-Regular, Menlo, monospace; background: var(--code); padding: 0.12em 0.35em; border-radius: 4px; }
pre { background: var(--code); padding: 16px 18px; border-radius: 8px; overflow-x: auto; line-height: 1.45; margin: 0 0 1.2em; }
pre code { background: none; padding: 0; font-size: 0.78em; }
figure { margin: 1.6em 0; }
figure img { width: 100%; height: auto; border-radius: 10px; }
@media (min-width: 1000px) { figure { margin-left: -60px; margin-right: -60px; } }
footer { margin-top: 3em; padding-top: 1em; border-top: 1px solid var(--rule); color: var(--muted); font-size: 0.85em; }
@media (max-width: 600px) { body { font-size: 18px; } h1 { font-size: 1.7em; } }
""".replace("FONTS/", FONTS)

FIGURE = """<figure><picture><source media="(prefers-color-scheme: dark)" srcset="images/pipeline-dark.svg"><img src="images/pipeline-light.svg" alt="The five steps: read the C, mirror it in Lean, race the two, prove or refute, file the bug"></picture></figure>"""
CHART = """<figure><picture><source media="(prefers-color-scheme: dark)" srcset="images/findings-dark.svg"><img src="images/findings-light.svg" alt="The 55 bug records by area and by whether NumPy already knew about them"></picture></figure>"""


def render(md):
    out = subprocess.run(["gh", "api", "markdown", "-f", "mode=gfm", "-f", f"text={md}"], capture_output=True, text=True, check=True)
    return out.stdout


def main():
    md = open(os.path.join(DOCS, "article.md")).read()
    title = md.splitlines()[0].lstrip("# ").strip()
    body = render(md)
    # GitHub wraps headings in anchor markup; keep plain headings for the article.
    body = re.sub(r'<div class="markdown-heading"[^>]*>(<h[1-6])[^>]*>(.*?)</h([1-6])>.*?</div>', lambda m: f"{m.group(1)}>{re.sub(r'<a [^>]*class=\"anchor\".*?</a>', '', m.group(2))}</h{m.group(3)}>", body, flags=re.S)
    body = re.sub(r'<h([1-6])[^>]*>', r'<h\1>', body)
    body = re.sub(r'<a id="user-content-[^"]*"[^>]*></a>', "", body)
    # The pipeline figure goes after the list of five steps, and the chart before the list of serious bugs.
    body = body.replace("</ol>", "</ol>\n" + FIGURE, 1)
    body = body.replace("<p>Five of them are serious", CHART + "\n<p>Five of them are serious", 1)
    desc = "I copied part of NumPy's C code into the Lean 4 proof checker, raced it against the real library 7.5 million times and proved claims about it. It found 55 bugs, and 26 had never been reported."
    page = f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)} | Pragyaan Gaur</title>
<meta name="description" content="{html.escape(desc)}">
<meta name="author" content="Pragyaan Gaur">
<link rel="canonical" href="{URL}">
<meta property="og:type" content="article">
<meta property="og:title" content="{html.escape(title)}">
<meta property="og:description" content="{html.escape(desc)}">
<meta property="og:url" content="{URL}">
<meta property="og:image" content="{URL}images/og.png">
<meta name="twitter:card" content="summary_large_image">
<link rel="icon" href="https://pragyaangaur.dev/favicon.png">
<style>{CSS}</style>
</head>
<body>
<main>
{body}
<footer>Written by <a href="https://pragyaangaur.dev/">Pragyaan Gaur</a>. The code, the proofs and every bug record are in the <a href="https://github.com/pragyaangaur/NumPy-Lean-Check">NumPy-Lean-Check repository</a>.</footer>
</main>
</body>
</html>
"""
    open(os.path.join(DOCS, "index.html"), "w").write(page)
    print("wrote docs/index.html")


if __name__ == "__main__":
    main()

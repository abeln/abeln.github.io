#!/usr/bin/env python3
"""Build the site: convert every Markdown file to HTML with Pandoc.

Usage:
    python3 build.py

Each foo.md becomes foo.html in the same folder, preserving subfolders.
Re-run it whenever you edit or add a Markdown file.
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HEADER = ROOT / "header.html"

# MathJax 3 "full" build: includes every TeX extension, including amscd,
# so the \begin{CD} ... \end{CD} commutative-diagram syntax renders.
MATHJAX_URL = "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml-full.js"

# Pandoc flags:
#   --standalone          produce a full HTML page (<head>/<body>), not a fragment
#   --mathjax=URL         render math via the MathJax build at URL
#   --include-in-header   inline our CSS into every page
# Delete header.html (or the file below) for completely bare, unstyled HTML.
PANDOC_FLAGS = ["--standalone", f"--mathjax={MATHJAX_URL}"]
if HEADER.exists():
    PANDOC_FLAGS.append(f"--include-in-header={HEADER}")


def main() -> None:
    # Convert every .md except README.md (that one stays the repo's readme).
    md_files = sorted(p for p in ROOT.rglob("*.md") if p.name != "README.md")
    if not md_files:
        print("No Markdown files found.")
        return

    for md in md_files:
        html = md.with_suffix(".html")
        print(f"  {md.relative_to(ROOT)}  ->  {html.relative_to(ROOT)}")
        subprocess.run(
            ["pandoc", str(md), *PANDOC_FLAGS, "-o", str(html)],
            check=True,
        )

    print(f"Done — {len(md_files)} file(s) converted.")


if __name__ == "__main__":
    try:
        main()
    except FileNotFoundError:
        sys.exit("pandoc not found. Install it with:  brew install pandoc")
    except subprocess.CalledProcessError as exc:
        sys.exit(f"pandoc failed (exit {exc.returncode}).")

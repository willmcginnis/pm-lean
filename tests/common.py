"""Shared helpers for the regression tests: the repository root, the docs, the counts script."""
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
DATA = ROOT / "data"

# The ledgers with a per-proposition row for ✱11–✱22, and the chapters fidelity_counts.py reads.
STAR_LEDGERS = ["star11", "star12", "star13", "star14", "star20", "star21", "star22"]
COUNTED = ["star11", "star13", "star14", "star20", "star21", "star22"]


def ledger(name):
    return json.loads((DATA / f"{name}_ledger.json").read_text(encoding="utf-8"))


def docs_text():
    """README.md and every Markdown file under docs/, concatenated: claims may move between them."""
    files = [ROOT / "README.md"] + sorted((ROOT / "docs").rglob("*.md"))
    return "\n".join(f.read_text(encoding="utf-8") for f in files if f.exists())


def find_script(name):
    """A script of the repository by file name, wherever it lives (data/, scripts/, ...)."""
    hits = [p for p in ROOT.rglob(name) if ".lake" not in p.parts and "tests" not in p.parts]
    if len(hits) != 1:
        raise FileNotFoundError(f"expected one {name} in the repository, found {hits}")
    return hits[0]


def run(cmd, timeout=1800):
    """Run a command at the repository root; return (exit code, stdout + stderr)."""
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout + p.stderr

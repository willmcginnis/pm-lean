#!/usr/bin/env python3
"""Count the PM-numbered theorems of Metamath's set.mm and iset.mm.

    python3 count_setmm.py CLONE [COMMIT]

CLONE is a git clone of https://github.com/metamath/set.mm (a partial
clone, `git clone --filter=blob:none --no-checkout`, is enough); COMMIT
defaults to the pin recorded as sources.setmm in data/roadmap.json. Both
databases are read at that commit with `git show`, so the counts do not
depend on the clone's checkout.

The convention, as cited in data/roadmap.json:
  - the file is split into whitespace-separated tokens, as Metamath does;
  - comments, from a `$(` token to the next `$)` token, are dropped;
  - a theorem is a label token followed by a `$p` token (axioms, `$a`,
    and hypotheses, `$e` and `$f`, are not counted);
  - "PM-numbered" means the label matches pm[0-9]+\\. (pm2.43, pm11.07,
    pm54.43 ...), and ✱1–✱5 means pm[1-5]\\. ; a bare `pm` prefix would
    also match unrelated labels and is not used.
"""

import collections
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PM_LABEL = re.compile(r"pm([0-9]+)\.")


def theorems(text):
    """The labels of the $p statements of a Metamath database, in order."""
    out = []
    in_comment = False
    prev = None
    for tok in text.split():
        if in_comment:
            if tok == "$)":
                in_comment = False
            continue
        if tok == "$(":
            in_comment = True
            continue
        if tok == "$p" and prev is not None:
            out.append(prev)
        prev = tok
    return out


def counts(labels):
    by_number = collections.Counter()
    for lab in labels:
        m = PM_LABEL.match(lab)
        if m:
            by_number[int(m.group(1))] += 1
    return {
        "pm_numbered": sum(by_number.values()),
        "pm1_to_pm5": sum(n for k, n in by_number.items() if 1 <= k <= 5),
        "pm10_to_pm14": sum(n for k, n in by_number.items() if 10 <= k <= 14),
        "by_number": dict(sorted(by_number.items())),
    }


def main(argv):
    if len(argv) not in (2, 3):
        print(__doc__, file=sys.stderr)
        return 2
    clone = argv[1]
    if len(argv) == 3:
        commit = argv[2]
    else:
        with open(os.path.join(ROOT, "data", "roadmap.json"), encoding="utf-8") as f:
            commit = json.load(f)["sources"]["setmm"]["commit"]
    result = {"commit": commit}
    for db in ("set.mm", "iset.mm"):
        text = subprocess.run(
            ["git", "-C", clone, "show", f"{commit}:{db}"],
            check=True, capture_output=True, text=True).stdout
        result[db] = counts(theorems(text))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

#!/usr/bin/env python3
"""Progress of the formalization, for docs/PROGRESS.md. Reads only this repository's files.
Done counts come from the committed files at a git revision (default HEAD: its PM/*.lean files and
data/*_ledger.json), never the working tree; totals come from PM's own numbered items:
  Vol I   data/vol1_items.json (assertions, Df, Pp, rules in words, per range; scripts/vol1_items.py);
  Vol II  data/vol2_labels.json, the distinct ✱-labels printed in bold in Project Gutenberg eBook #78255's
          HTML: an upper bound, definitions included;
  Vol III not counted (the Distributed Proofreaders text is not yet published).
Done uses the rules of docs/FORMALIZATION_COMPARISON.md:
  stated   an assertion with a theorem named for its PM number (t<c>_<d> for ✱2–✱5, q<c>_<d> from ✱9 on);
  proved   stated, in files with no sorry / axiom / native_decide, and not merely a primitive rule restated
           (the build and #print axioms are checked separately: AxiomCheck.lean, AllAxioms.lean);
  followed stated and proved, with a per-proposition ledger row saying the proof follows PM's (pm-lines or
           pm-lines+extra; replay_ledger.json's FAITHFUL / REPAIRED); ranges without a ledger count 0 and are flagged.

Usage: python3 scripts/progress.py [--ref REV] [--update] [--vol2-html PATH]
  prints the tables; --update replaces the block between <!-- progress:start --> and <!-- progress:end -->
  in docs/PROGRESS.md; --vol2-html PATH (pg78255-images.html) first rewrites data/vol2_labels.json from it."""
import json, os, re, subprocess, sys

R = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_GIT = R
LEAN_REF = "HEAD"
IDS = os.path.join(R, "data/vol1_items.json")
VOL2_LABELS = os.path.join(R, "data/vol2_labels.json")
FOLLOWS = ("pm-lines", "pm-lines+extra")
UNSOUND = re.compile(r"\bsorry\b|^axiom\s|native_decide", re.M)
# display ranges for Vol I, built from data/vol1_items.json's ranges
VOL1_RANGES = [("✱1–✱5", ("1", "2-5")), ("✱9–✱14", ("9", "10", "11-14")),
               ("✱20–✱56", ("20-56",)), ("✱60–✱97", ("60-97",))]


SUBJECT = {2: "immediate consequences of the primitive propositions", 3: "the logical product of two propositions",
           4: "equivalence and formal rules", 5: "miscellaneous propositions", 9: "extension of the theory of deduction from lower "
           "to higher types of propositions", 10: "theory of propositions containing one apparent variable",
           11: "theory of two apparent variables", 13: "identity", 14: "descriptions", 20: "general theory of classes",
           21: "general theory of relations"}


def git(*a):
    return subprocess.run(["git", "-C", LEAN_GIT, *a], check=True, capture_output=True, text=True).stdout


def LG(path):
    return git("show", f"{LEAN_REF}:{path}")


def bar(p, w=20):
    n = round(p * w / 100)
    return "█" * n + "░" * (w - n)


def pct(a, b):
    return round(100 * a / b, 1) if b else None


def vol2_labels_from_html(path):
    """Distinct ✱N·M labels in bold (<b>✱N·M.</b>, also combined ones such as ✱106·4·41·411 and misprinted
    separators such as ✱102*74), with the page of their first bold occurrence."""
    t = open(path, encoding="utf-8").read()
    labels, page = {}, None
    for m in re.finditer(r'id="Page_(\d+)"|<b>(.*?)</b>', t, re.S):
        if m.group(1):
            page = int(m.group(1)); continue
        s = re.sub(r"</?a[^>]*>", "", m.group(2)).strip()
        mm = re.fullmatch(r"\*(\d+)((?:\s*[·.*\-]\s*\*?\d+)+)\s*\.?", s)
        if not mm: continue
        c = int(mm.group(1))
        for d in re.findall(r"\d+", mm.group(2)):
            labels.setdefault((c, d), page)
    return labels


def write_vol2_labels(labels):
    rows = [{"chapter": c, "number": d, "page": p} for (c, d), p in labels.items()]
    with open(VOL2_LABELS, "w", encoding="utf-8") as f:
        f.write("[\n" + ",\n".join(json.dumps(r) for r in rows) + "\n]\n")


def vol2_labels():
    """data/vol2_labels.json, in order of first bold occurrence: (chapter, number) -> page."""
    return {(r["chapter"], r["number"]): r["page"] for r in json.load(open(VOL2_LABELS, encoding="utf-8"))}


def compute():
    ids = json.load(open(IDS, encoding="utf-8"))
    cat = {x["id"]: x["cat"] for x in ids}
    rng = {x["id"]: x["range"] for x in ids}
    pages = {x["id"]: x["page"] for x in ids}
    ch = lambda i: int(i[1:].split(".")[0])
    files = [f for f in git("ls-tree", "-r", "--name-only", LEAN_REF, "PM/").split() if f.endswith(".lean")]
    src = {f: LG(f) for f in files}
    stated, proved, followed = set(), set(), set()

    # ✱2–✱5: Replay.lean / Replay2.lean, ledgers replay_ledger.json (tags) and replay2_ledger.json (fidelity)
    r1 = {x["id"]: x for x in json.loads(LG("data/replay_ledger.json"))}
    r2 = {x["id"]: x for x in json.loads(LG("data/replay2_ledger.json"))}
    for f in ("PM/Replay.lean", "PM/Replay2.lean"):
        clean = not UNSOUND.search(src[f])
        for c, d in re.findall(r"^theorem t(\d+)_(\d+)\b", src[f], re.M):
            i = f"*{c}.{d}"
            if cat.get(i) != "assertion": continue
            stated.add(i)
            if clean: proved.add(i)
            if clean and (r2[i]["fidelity"] in FOLLOWS if i in r2 else r1[i]["tag"] in ("FAITHFUL", "REPAIRED")):
                followed.add(i)

    # ✱9–✱10: Star10.lean; no per-proposition ledger. A proof that is one primitive rule of the embedding
    # (QThm.inst/gen/distrib/mp, or q10_1/q10_12 applied to variables) restates a primitive: stated, not proved.
    s10 = src["PM/Star10.lean"]
    restated = []
    alld = list(re.finditer(r"^theorem\s+(q\d+_\w+)", s10, re.M))
    for k, m in enumerate(alld):
        mm = re.fullmatch(r"q(\d+)_(\d+)", m.group(1))
        if not mm: continue
        i = f"*{mm.group(1)}.{mm.group(2)}"
        if cat.get(i) != "assertion": continue
        body = s10[m.end():alld[k + 1].start() if k + 1 < len(alld) else len(s10)].split(":=", 1)[1]
        body = re.split(r"\n/--|\n/-!", body)[0].strip()
        stated.add(i)
        if re.fullmatch(r"(QThm\.(inst|gen|distrib|mp)|q10_1|q10_12)( [\wφψχ]+)*", body):
            restated.append(i)
        elif not UNSOUND.search(s10):
            proved.add(i)

    # ✱11 onward, all volumes: q<c>_<d> (variant q<c>_<d>_neg counts once) in any PM file, ledgers star<c>_ledger.json
    ledgers = [f for f in git("ls-tree", "-r", "--name-only", LEAN_REF, "data/").split()
               if re.fullmatch(r"data/star\d+_ledger\.json", f)]
    led = {x["id"]: x for f in ledgers for x in json.loads(LG(f))}
    later = {}   # chapter >= 11 not in Vol I's list: Vol II/III
    for f, s in src.items():
        if f == "PM/Star10.lean": continue
        clean = not UNSOUND.search(s)
        for c, d in re.findall(r"^theorem\s+q(\d+)_(\d+)(?:_neg)?\b(?!_)", s, re.M):
            if int(c) < 11: continue
            i = f"*{c}.{d}"
            if int(c) > 97:
                later.setdefault(i, clean); continue
            if cat.get(i) != "assertion": continue
            stated.add(i)
            if clean: proved.add(i)
            if clean and i in led and led[i]["fidelity"] in FOLLOWS: followed.add(i)
    ledgered_ranges = {rng[i] for i in led if i in rng} | {"2-5"}

    def cell(ranges):
        A = [i for i, c in cat.items() if c == "assertion" and rng[i] in ranges]
        o = {"assertions": len(A),
             "Df": sum(cat[i] == "Df" and rng[i] in ranges for i in cat),
             "Pp": sum(cat[i] == "Pp" and rng[i] in ranges for i in cat),
             "rules_in_words": sum(cat[i] == "rule/prose" and rng[i] in ranges for i in cat),
             "stated": len(stated & set(A)), "proved": len(proved & set(A)), "followed": len(followed & set(A)),
             "followed_not_recorded_ranges": [r for r in ranges if r not in ledgered_ranges
                                              and any(rng[i] == r for i in stated)]}
        o["items"] = o["assertions"] + o["Df"] + o["Pp"] + o["rules_in_words"]
        o["proved_pct"] = pct(o["proved"], o["assertions"])
        return o

    by_range = {name: cell(rs) for name, rs in VOL1_RANGES}
    vol1 = cell(tuple(r for _, rs in VOL1_RANGES for r in rs))
    vol1["chapters"] = [min(ch(i) for i in cat), max(ch(i) for i in cat)]
    assert vol1["items"] == len(ids), (vol1["items"], len(ids))
    # chapters with at least one stated item
    by_chapter = []
    for c in sorted({ch(i) for i in stated}):
        A = {i for i in cat if ch(i) == c and cat[i] == "assertion"}
        pg = [pages[i] for i in cat if ch(i) == c and pages[i]]
        by_chapter.append({"chapter": c, "pages": [min(pg), max(pg)], "assertions": len(A),
                           "stated": len(stated & A), "proved": len(proved & A), "followed": len(followed & A),
                           "ledger": 2 <= c <= 5 or any(i in led for i in A)})

    lab = vol2_labels()
    v2 = {k: p for k, p in lab.items() if 100 <= k[0] <= 234}
    v2_ids = {f"*{c}.{d}" for c, d in v2}
    vol2 = {"labels_upper_bound": len(v2), "chapters": [min(c for c, _ in v2), max(c for c, _ in v2)],
            "labels_outside_100_234": sorted(f"*{c}.{d}" for c, d in lab if not 100 <= c <= 234),
            "stated": len([i for i in later if i in v2_ids]), "proved": len([i for i in later if i in v2_ids and later[i]]),
            "followed": len([i for i in later if i in v2_ids and later[i] and i in led and led[i]["fidelity"] in FOLLOWS])}
    vol2["proved_pct"] = pct(vol2["proved"], vol2["labels_upper_bound"])
    vol3 = {"total": None, "stated": len([i for i in later if ch(i) > vol2["chapters"][1]]),
            "proved": len([i for i in later if ch(i) > vol2["chapters"][1] and later[i]])}

    # milestones
    def chap(lo, hi=None):
        hi = hi or lo
        A = [i for i, c in cat.items() if c == "assertion" and lo <= ch(i) <= hi]
        P = [i for i in A if i in proved]
        pg = [pages[i] for i, c in cat.items() if lo <= ch(i) <= hi and pages[i]]
        return A, P, [min(pg), max(pg)]

    def status(total, done):
        return "done" if total and done == total else ("in progress" if done else "not started")

    ms = []
    star12 = [i for i in cat if ch(i) == 12]
    pp12 = [i for i in star12 if cat[i] == "Pp"]
    a12, _, pg12 = chap(12)
    ok12 = not a12 and all(led.get(i, {}).get("category") == "primitive" for i in pp12)
    ms.append({"key": "types", "what": "Types and reducibility (✱12)", "pages": pg12, "volume": "I",
               "status": "done" if ok12 else "not started",
               "detail": f"✱12 has no assertions; its primitive propositions {' and '.join(lbl(i) for i in pp12)} are "
               "rules of the system" if ok12 else None, "pp": pp12})
    A, P, pg = chap(14)
    # proved only as a schema (one theorem per instance), as a section heading of the Lean file says
    schema = sorted(i for i in P if any(f"/-! ## {lbl(i)} as a schema -/" in s for s in src.values()))
    ms.append({"key": "descriptions", "what": "Descriptions (✱14)", "pages": pg, "volume": "I",
               "status": status(len(A), len(P)), "proved": len(P), "total": len(A),
               "not_proved": sorted(set(A) - set(P), key=lambda i: [int(x) for x in i[1:].split(".")]),
               "as_schema": schema})
    A, P, pg = chap(20, 24)
    ms.append({"key": "classes", "what": "Classes (✱20–✱24)", "pages": pg, "volume": "I",
               "status": status(len(A), len(P)), "proved": len(P), "total": len(A),
               "proved_by_chapter": {f"*{c}": len(chap(c)[1]) for c in range(20, 25)},
               "total_by_chapter": {f"*{c}": len(chap(c)[0]) for c in range(20, 25)},
               "not_proved_started": sorted((i for i in set(A) - set(P) if len(chap(ch(i))[1])),
                                            key=lambda i: [int(x) for x in i[1:].split(".")])})
    A54, P54, _ = chap(54)
    ms.append({"key": "54.43", "what": "✱54·43, the step before 1+1=2", "pages": [pages["*54.43"]] * 2, "volume": "I",
               "status": "done" if "*54.43" in proved else ("in progress" if P54 else "not started"),
               "chapter_54_proved": len(P54), "chapter_54_total": len(A54)})
    _, _, pg97 = chap(97)
    ms.append({"key": "end1", "what": "End of Vol I (✱97)", "pages": [pg97[1]] * 2, "volume": "I",
               "status": status(vol1["assertions"], vol1["proved"]), "proved": vol1["proved"], "total": vol1["assertions"]})
    i110 = "*110.643"
    ms.append({"key": "110.643", "what": "✱110·643, 1+1=2", "pages": [v2[(110, "643")]] * 2, "volume": "II",
               "status": "done" if i110 in later and later[i110] else
               ("in progress" if any(ch(i) == 110 for i in later) else "not started")})
    last = max((k for k in v2 if k[0] == vol2["chapters"][1]), key=lambda k: v2[k])
    ms.append({"key": "end2", "what": f"End of Vol II (✱{vol2['chapters'][1]})", "pages": [v2[last]] * 2,
               "volume": "II", "status": "in progress" if vol2["proved"] else "not started"})
    ms.append({"key": "end3", "what": "End of Vol III", "pages": None, "volume": "III",
               "status": "in progress" if vol3["proved"] else "not started"})

    return {"lean_ref": LEAN_REF, "lean_commit": git("rev-parse", "--short", LEAN_REF).strip(),
            "vol1": vol1, "vol1_by_range": by_range, "vol2": vol2, "vol3": vol3,
            "restated_primitives": sorted(restated, key=lambda i: [int(x) for x in i[1:].split(".")]), "ledgers": sorted(ledgers + ["data/replay_ledger.json",
                                                                                   "data/replay2_ledger.json"]),
            "milestones": ms, "vol1_by_chapter": by_chapter}


def fmt_pages(m):
    p = m["pages"]
    if not p: return "not yet counted"
    return f"Vol {m['volume']}, p. {p[0]}" if p[0] == p[1] else f"Vol {m['volume']}, pp. {p[0]}–{p[1]}"


def n(x):
    return f"{x:,}"


def lbl(i):
    return i.replace("*", "✱").replace(".", "·")


def show_pct(p):
    return "0%" if p == 0 else f"{p}%"


def markdown(d):
    v1, v2, v3 = d["vol1"], d["vol2"], d["vol3"]
    sym = {"done": "✅ done", "in progress": "🟡 in progress", "not started": "⬜ not started"}
    L = []
    L.append(f"Generated by `scripts/progress.py` from the files at commit `{d['lean_commit']}`; no dates are "
             "estimated. The unit is one of PM's numbered assertions, and "
             "**stated / proved / followed PM's lines** mean the same as S / P / F in the "
             "[formalization table](FORMALIZATION_COMPARISON.md). The counts come from the Lean files' theorem "
             "names and the ledgers; that the proofs check comes from building them. The bar shows the share "
             "proved. Footnotes ᵃ–ᵉ are below the tables.")
    L.append("")
    L.append("| | Stated | Proved | Followed PM's lines | Total in PM | Proved share |")
    L.append("|---|---|---|---|---|---|")
    L.append(f"| **Vol I** (✱{v1['chapters'][0]}–✱{v1['chapters'][1]}) | {n(v1['stated'])} | {n(v1['proved'])} | "
             f"{n(v1['followed'])}ᵃ | {n(v1['assertions'])} assertionsᵇ | `{bar(v1['proved_pct'])}` {show_pct(v1['proved_pct'])} |")
    L.append(f"| **Vol II** (✱{v2['chapters'][0]}–✱{v2['chapters'][1]}) | {n(v2['stated'])} | {n(v2['proved'])} | "
             f"{n(v2['followed'])} | at most {n(v2['labels_upper_bound'])} numbered itemsᶜ | "
             f"`{bar(v2['proved_pct'])}` {show_pct(v2['proved_pct'])} |")
    L.append(f"| **Vol III** | {n(v3['stated'])} | {n(v3['proved'])} | 0 | not yet countedᵈ | — |")
    L.append("")
    L.append("Vol I by range:")
    L.append("")
    L.append("| Range | Stated | Proved | Followed PM's lines | Assertions | Also numbered (Df / Pp / rules in words) | Proved share |")
    L.append("|---|---|---|---|---|---|---|")
    for name, c in d["vol1_by_range"].items():
        fn = "ᵃ" if c["followed_not_recorded_ranges"] else ""
        bp = f"`{bar(c['proved_pct'])}` {show_pct(c['proved_pct'])}" if c["assertions"] else "—"
        L.append(f"| {name} | {n(c['stated'])} | {n(c['proved'])} | {n(c['followed'])}{fn} | {n(c['assertions'])} | "
                 f"{c['Df']} / {c['Pp']} / {c['rules_in_words']} | {bp} |")
    L.append("")
    L.append("Vol I by chapter (chapters with at least one statement):")
    L.append("")
    L.append("| Chapter | Subject | Pages (1910) | Stated | Proved | Followed PM's lines | Assertions |")
    L.append("|---|---|---|---|---|---|---|")
    for c in d["vol1_by_chapter"]:
        L.append(f"| ✱{c['chapter']} | {SUBJECT.get(c['chapter'], '')} | {c['pages'][0]}–{c['pages'][1]} | "
                 f"{c['stated']} | {c['proved']} | {c['followed'] if c['ledger'] else 'nsᵃ'} | {c['assertions']} |")
    L.append("")
    L.append("Milestonesᵉ:")
    L.append("")
    L.append("| Milestone | Page in the print (Vol I 1910, Vol II 1912) | Status |")
    L.append("|---|---|---|")
    for m in d["milestones"]:
        s = sym[m["status"]]
        if m["key"] == "types": s += f": {m['detail']}"
        elif m["key"] in ("descriptions", "classes", "end1") and m["status"] != "not started":
            s += f": {n(m['proved'])} of {n(m['total'])} assertions proved"
            if m["key"] == "descriptions" and m["not_proved"]:
                s += f" (not {', '.join(lbl(x) for x in m['not_proved'])})"
            if m["key"] == "descriptions" and m.get("as_schema"):
                # the reason is the one docs/PROGRESS.md and PM/Star14.lean give; fail rather than print a stale one
                why = {"*14.3": "its printed form has p, q as apparent variables, which needs a type of "
                       "propositions the 1910 encoding does not have"}
                assert set(m["as_schema"]) <= set(why), m["as_schema"]
                s += "; " + "; ".join(f"{lbl(i)} as a schema (one theorem per instance), not as printed: {why[i]}"
                                      for i in m["as_schema"])
            if m["key"] == "classes":
                started = [c for c in m["proved_by_chapter"] if m["proved_by_chapter"][c]]
                rest = [c for c in m["proved_by_chapter"] if not m["proved_by_chapter"][c]]
                s += " (" + ", ".join(f"{lbl(c)} {m['proved_by_chapter'][c]} of {m['total_by_chapter'][c]}"
                                      for c in started)
                if rest: s += f"; {lbl(rest[0])}–{lbl(rest[-1])} not started" if len(rest) > 1 else f"; {lbl(rest[0])} not started"
                s += ")"
                # the reasons are the ones PM/Star20.lean and PM/Star21.lean give; fail rather than print stale ones
                why = {("*20.631", "*20.632", "*21.631", "*21.632"): "about significance, built into the syntax "
                       "like ✱10·121 and ✱10·122, so not counted as proved"}
                assert set(m["not_proved_started"]) == {i for k in why for i in k}, m["not_proved_started"]
                s += ". Not counted: " + "; ".join(f"{', '.join(lbl(i) for i in k)} ({w})" for k, w in why.items())
        L.append(f"| {m['what']} | {fmt_pages(m)} | {s} |")
    L.append("")
    nr = [r for c in d["vol1_by_range"].values() for r in c["followed_not_recorded_ranges"]]
    L.append("ᵃ Counted only where this repository keeps a per-proposition ledger. "
             + ("✱9–✱10 have none (\"ns\" in the [formalization table](FORMALIZATION_COMPARISON.md)), so they add 0 here. " if set(nr) >= {"9", "10"} else "")
             + f"{len(d['restated_primitives'])} stated items "
             f"({', '.join(lbl(x) for x in d['restated_primitives'])}) are primitive rules "
             "of the system, so they are not counted as proved.")
    L.append(f"ᵇ Counted from the Gutenberg #78050 text with a few corrections (`data/vol1_items.json`), as in the formalization table: "
             f"{n(v1['items'])} numbered items, of which {n(v1['assertions'])} are assertions, {v1['Df']} definitions, "
             f"{v1['Pp']} primitive propositions and {v1['rules_in_words']} rules stated in words. Only assertions "
             "are counted as done or total.")
    L.append(f"ᶜ An upper bound, not a count of assertions: the distinct ✱{v2['chapters'][0]}–✱{v2['chapters'][1]} "
             "labels printed in bold in the Gutenberg #78255 transcription (`data/vol2_labels.json`), definitions included (a label repeated in "
             "a quotation counts once), not checked item by item. It will be replaced when a per-item list of Vol II is built.")
    L.append("ᵈ The Distributed Proofreaders text of Vol III is not yet published, so its items have not been "
             "counted here.")
    L.append("ᵉ Pages are those of the first and last numbered item concerned, from the same lists as the totals. "
             "A milestone is done when every assertion in it is proved, in progress when some are, and not started "
             "when none are; a single proposition is in progress when its chapter has proved assertions.")
    # a blank line between footnotes, so that each renders as its own paragraph
    out = []
    for x in L:
        if x and x[0] in "ᵇᶜᵈᵉ": out.append("")
        out.append(x)
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    args = sys.argv[1:]
    if "--ref" in args:
        LEAN_REF = args[args.index("--ref") + 1]
    if "--vol2-html" in args:
        write_vol2_labels(vol2_labels_from_html(args[args.index("--vol2-html") + 1]))
    md = markdown(compute())
    if "--update" in args:
        p = os.path.join(R, "docs/PROGRESS.md")
        t = open(p, encoding="utf-8").read()
        a, b = "<!-- progress:start -->\n", "<!-- progress:end -->"
        assert t.count(a) == 1 and t.count(b) == 1, "markers missing"
        t = t.split(a)[0] + a + md + b + t.split(b)[1]
        open(p, "w", encoding="utf-8").write(t)
    print(md)

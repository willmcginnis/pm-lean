"""The external checkers (scripts/external_checkers.py, docs/VERIFICATION.md, "External checkers").

Where they run: a step of tests/run_all.sh and of scripts/release_check.sh, which fails on a nonzero exit
and also requires nanoda's pin to be upstream's head; the release check runs the standing checks without
them, so they run once. The scan of the export, the gate that nanoda's configuration relies on, is tested
on small hand-written exports in lean4export's format, one seeded fault per rule; no Lean or checker
runs here (the script itself runs the seeded faults through both checkers, its negative controls).
"""
import importlib.util
import json
import os
import re
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT

spec = importlib.util.spec_from_file_location("external_checkers", ROOT / "scripts" / "external_checkers.py")
ext = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ext)

SEVEN = ["propext", "Quot.sound", "Classical.choice", "sorryAx", "Lean.trustCompiler", "Lean.ofReduceBool",
         "Lean.ofReduceNat"]


class Export:
    """A small export in lean4export's format: names, then expressions and declarations in order."""

    def __init__(self):
        self.lines, self.names, self.exprs = [], {}, 0
        self.lines.append(json.dumps({"meta": {"format": {"version": "3.1.0"}}}))
        self.expr({"sort": 0})

    def name(self, full):
        pre = 0
        for i, part in enumerate(full.split(".")):
            key = ".".join(full.split(".")[:i + 1])
            if key not in self.names:
                self.names[key] = len(self.names) + 1
                if part.isdigit():
                    self.lines.append(json.dumps({"in": self.names[key], "num": {"i": int(part), "pre": pre}},
                                                 sort_keys=True, separators=(",", ":")))
                else:
                    self.lines.append(json.dumps({"in": self.names[key], "str": {"pre": pre, "str": part}},
                                                 sort_keys=True, separators=(",", ":")))
            pre = self.names[key]
        return pre

    def expr(self, body):
        i = self.exprs
        self.exprs += 1
        self.lines.append(json.dumps(dict(body, ie=i), sort_keys=True, separators=(",", ":")))
        return i

    def const(self, full):
        return self.expr({"const": {"name": self.name(full), "us": []}})

    def app(self, f, a):
        return self.expr({"app": {"fn": f, "arg": a}})

    def decl(self, kind, full, type_=0, value=None):
        body = {"name": self.name(full), "levelParams": [], "type": type_}
        if kind != "axiom":
            body["all"] = [body["name"]]
        if value is not None:
            body["value"] = value
        self.lines.append(json.dumps({kind: body}, sort_keys=True, separators=(",", ":")))

    def inductive(self, full, rhs):
        n, ctor, rec = self.name(full), self.name(full + ".mk"), self.name(full + ".rec")
        self.lines.append(json.dumps({"inductive": {
            "types": [{"name": n, "type": 0, "all": [n], "ctors": [ctor]}],
            "ctors": [{"name": ctor, "induct": n, "type": 0}],
            "recs": [{"name": rec, "type": 0, "rules": [{"ctor": ctor, "nfields": 0, "rhs": rhs}]}]}},
            sort_keys=True, separators=(",", ":")))

    def core(self):
        """Lean core's seven axioms, and the two opaque constants whose bodies name Lean.trustCompiler."""
        for a in SEVEN:
            self.decl("axiom", a)
        for o in ("Lean.reduceBool", "Lean.reduceNat"):
            self.decl("opaque", o, 0, self.app(self.const("Lean.trustCompiler"), 0))
        return self

    def scan(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "export.ndjson")
            with open(path, "w") as f:
                f.write("\n".join(self.lines) + "\n")
            return ext.scan_export(path)


class Scan(unittest.TestCase):
    def fails_with(self, export, reason, user):
        ok, rep = export.scan()
        self.assertFalse(ok, f"the scan passed an export where {user} names {reason}")
        hits = [r for r in rep["reasons"] if r.startswith(reason)]
        self.assertTrue(hits, rep["reasons"])
        self.assertIn(user, hits[0])

    def test_core_alone_passes(self):
        e = Export().core()
        e.decl("thm", "PM.fine", 0, e.app(e.const("propext"), 0))
        ok, rep = e.scan()
        self.assertTrue(ok, rep["reasons"])
        self.assertEqual(rep["axioms"], sorted(SEVEN))
        self.assertEqual(rep["users"]["Lean.trustCompiler"], ["Lean.reduceBool", "Lean.reduceNat"])

    def test_sorry_through_an_expression(self):
        e = Export().core()
        inner = e.app(e.const("sorryAx"), 0)
        e.decl("thm", "PM.bad", 0, e.app(e.app(e.const("PM.fine"), inner), 0))
        self.fails_with(e, "sorryAx", "PM.bad")

    def test_sorry_in_a_type(self):
        e = Export().core()
        e.decl("def", "PM.bad", e.app(e.const("sorryAx"), 0), 0)
        self.fails_with(e, "sorryAx", "PM.bad")

    def test_sorry_in_a_recursor_rule(self):
        e = Export().core()
        e.inductive("PM.Bad", e.app(e.const("sorryAx"), 0))
        self.fails_with(e, "sorryAx", "PM.Bad")

    def test_stray_axiom(self):
        e = Export().core()
        e.decl("axiom", "PM.stray")
        self.fails_with(e, "axiom", "PM.stray")

    def test_reduce_bool_and_nat(self):
        for ax in ("Lean.ofReduceBool", "Lean.ofReduceNat"):
            e = Export().core()
            e.decl("thm", "PM.bad", 0, e.app(e.const(ax), 0))
            self.fails_with(e, ax, "PM.bad")

    def test_trust_compiler_elsewhere(self):
        e = Export().core()
        e.decl("thm", "PM.bad", 0, e.const("Lean.trustCompiler"))
        self.fails_with(e, "Lean.trustCompiler", "PM.bad")

    def test_numeric_name_component(self):
        e = Export().core()
        e.decl("thm", "PM.bad.1", 0, e.const("sorryAx"))
        self.fails_with(e, "sorryAx", "PM.bad.1")


class Configuration(unittest.TestCase):
    """The pins, nanoda's configuration and the negative controls change only deliberately."""

    def test_pins(self):
        doc = (ROOT / "docs" / "VERIFICATION.md").read_text(encoding="utf-8")
        for name, (url, rev, _) in ext.TOOLS.items():
            self.assertRegex(rev, r"^[0-9a-f]{40}$")
            self.assertTrue(f"`{rev[:7]}`" in doc, f"docs/VERIFICATION.md does not name {name}'s pin")
        self.assertEqual(ext.TARGETS, ["PM", "Checks.PinnedStatements"])

    def test_nanoda_configuration(self):
        self.assertEqual(sorted(ext.NANODA_CONFIG["permitted_axioms"]),
                         ["Classical.choice", "Lean.trustCompiler", "Quot.sound", "propext"])
        self.assertIs(ext.NANODA_CONFIG["unpermitted_axiom_hard_error"], False)
        self.assertEqual(ext.CORE_AXIOMS, set(SEVEN))
        self.assertEqual(ext.TRUST_COMPILER_USERS, {"Lean.reduceBool", "Lean.reduceNat"})

    def test_a_control_for_each_rule(self):
        reasons = {c[4] for c in ext.CONTROLS}
        self.assertEqual(reasons, {"axiom", "sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat",
                                   "Lean.trustCompiler"})
        both = {c[0]: c[3] for c in ext.CONTROLS}
        for module in ("NegSorry", "NegAxiom"):
            self.assertEqual(both[module], {"con-leche", "nanoda", "scan"})
        for module, _, theorem, rejectors, _ in ext.CONTROLS:
            self.assertIn("scan", rejectors, module)


class Wiring(unittest.TestCase):
    def test_run_all_and_release_check(self):
        run_all = (ROOT / "tests" / "run_all.sh").read_text(encoding="utf-8")
        self.assertRegex(run_all, r"\n\s*python3 scripts/external_checkers\.py \|\| fail ")
        release = (ROOT / "scripts" / "release_check.sh").read_text(encoding="utf-8")
        self.assertRegex(release, r"\npython3 scripts/external_checkers\.py --nanoda-upstream require "
                                  r"\|\| fail ")
        self.assertRegex(release, r"\n\s*SKIP_EXTERNAL=1 bash tests/run_all\.sh \|\| fail ")
        step = re.search(r'if \[ -z "\$\{SKIP_EXTERNAL:-\}" \]; then\n(.*?)\nfi\n', run_all, re.S)
        self.assertIsNotNone(step, "run_all.sh: the step is not behind SKIP_EXTERNAL")
        self.assertIn("python3 scripts/external_checkers.py", step.group(1))


if __name__ == "__main__":
    unittest.main()

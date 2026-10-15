"""The external checkers (scripts/external_checkers.py, docs/VERIFICATION.md, "External checkers").

Where they run: a step of tests/run_all.sh and of scripts/release_check.sh, which fails on a nonzero exit
and also requires nanoda's pin to be upstream's head; the release check runs the standing checks without
them, so they run once. The scan of the export, the gate that nanoda's configuration relies on, is tested
on small hand-written exports in lean4export's format, one seeded fault per rule; no Lean or checker
runs here (the script itself runs the seeded faults through both checkers, its negative controls).
"""
import contextlib
import importlib.util
import io
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
        """`full` dotted, a digit-only component numeric; or a tuple of components as ext.N gives."""
        parts = full if isinstance(full, tuple) else \
            ext.N(*(int(p) if p.isdigit() else p for p in full.split(".")))
        pre = 0
        for i in range(len(parts)):
            key = parts[:i + 1]
            if key not in self.names:
                self.names[key] = len(self.names) + 1
                kind, v = parts[i]
                body = {"i": v, "pre": pre} if kind == "num" else {"pre": pre, "str": v}
                self.lines.append(json.dumps({"in": self.names[key], kind: body}, sort_keys=True,
                                             separators=(",", ":")))
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

    def write(self, path):
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(self.lines) + "\n")

    def scan(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "export.ndjson")
            self.write(path)
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

    def test_counts(self):
        e = Export().core()
        e.inductive("PM.Ind", 0)
        e.decl("thm", "PM.fine", 0, 0)
        ok, rep = e.scan()
        self.assertTrue(ok, rep["reasons"])
        # 7 axioms, 2 opaque, 1 inductive (type, constructor, recursor), 1 theorem
        self.assertEqual((rep["declarations"], rep["expanded"]), (11, 13))
        self.assertEqual(rep["nanoda_skipped"], ["Lean.ofReduceBool", "Lean.ofReduceNat", "sorryAx"])
        self.assertEqual(rep["nanoda_expected"], 10)
        self.assertEqual(rep["namespaces"]["PM"], {"records": 2, "constants": 4})


class StructuredNames(unittest.TestCase):
    """Every rule of the scan compares names component by component. A one-component name whose text
    has a dot, written «Lean.reduceBool» in Lean, is not core's Lean.reduceBool; a scan that flattened
    names into dotted strings would pass the first two exports below (and did)."""

    def test_quoted_core_user_is_not_core(self):
        e = Export().core()
        e.decl("opaque", ext.N("Lean.reduceBool"), 0, e.const("Lean.trustCompiler"))
        e.decl("thm", "bad", 0, e.const(ext.N("Lean.reduceBool")))
        ok, rep = e.scan()
        self.assertFalse(ok, "the scan took a one-component «Lean.reduceBool» for core's Lean.reduceBool")
        hits = [r for r in rep["reasons"] if r.startswith("Lean.trustCompiler")]
        self.assertTrue(hits and "«Lean.reduceBool»" in hits[0], rep["reasons"])

    def test_quoted_standard_axiom_is_stray(self):
        e = Export().core()
        e.decl("axiom", ext.N("Classical.choice"))
        ok, rep = e.scan()
        self.assertFalse(ok, "the scan took a one-component «Classical.choice» for Classical.choice")
        self.assertIn("«Classical.choice»", rep["reasons"][0])
        self.assertTrue(rep["reasons"][0].startswith("axiom"))

    def test_quoted_never_named_is_another_constant(self):
        # a definition named «Lean.ofReduceBool», one component, is not the axiom: naming it is no fault
        e = Export().core()
        e.decl("def", ext.N("Lean.ofReduceBool"), 0, 0)
        e.decl("thm", "PM.fine", 0, e.const(ext.N("Lean.ofReduceBool")))
        ok, rep = e.scan()
        self.assertTrue(ok, rep["reasons"])

    def test_numeric_and_string_components_differ(self):
        e = Export()
        a, b = e.name(ext.N("x", 1)), e.name(ext.N("x", "1"))
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "export.ndjson")
            e.write(path)
            names = ext.read_names(path)
        self.assertEqual(names[a], (("str", "x"), ("num", 1)))
        self.assertEqual(names[b], (("str", "x"), ("str", "1")))
        self.assertEqual((ext.show(names[a]), ext.show(names[b])), ("x.1", "x.«1»"))

    def test_escaped_component_is_read_whole(self):
        # a component written with JSON escapes is the same name: here core's Lean.trustCompiler
        e = Export().core()
        lean = e.names[ext.N("Lean")]
        e.lines.append('{"in":900,"str":{"pre":%d,"str":"trust\\u0043ompiler"}}' % lean)
        e.decl("thm", "PM.bad", 0, e.expr({"const": {"name": 900, "us": []}}))
        ok, rep = e.scan()
        self.assertFalse(ok)
        self.assertIn("PM.bad", rep["users"]["Lean.trustCompiler"])

    def test_rules_hold_structured_names(self):
        for s in (ext.CORE_AXIOMS, ext.NEVER_NAMED, ext.WATCHED, ext.TRUST_COMPILER_USERS,
                  ext.NANODA_PERMITTED, {ext.TRUST_COMPILER}):
            for n in s:
                self.assertIsInstance(n, tuple)
                self.assertTrue(all(k in ("str", "num") for k, _ in n), n)
                self.assertFalse(any(k == "str" and "." in v for k, v in n), n)
        self.assertEqual(sorted(ext.show(n) for n in ext.NANODA_PERMITTED),
                         sorted(ext.NANODA_CONFIG["permitted_axioms"]))


class Reconciliation(unittest.TestCase):
    """main() with the tools, the build, the export, the scan and the controls replaced, and each
    checker's output injected: a wrong count, or a crash, must fail the step."""

    REP = {"passes": True, "declarations": 167603, "expanded": 175577, "nanoda_expected": 175574,
           "nanoda_skipped": ["Lean.ofReduceBool", "Lean.ofReduceNat", "sorryAx"],
           "axioms": sorted(SEVEN), "users": {}, "namespaces": {}, "reasons": []}
    CL_OK = (0, "con-leche: accepted 167603 declarations (--verified)\n", "")
    ND_OK = (0, "Checked 175574 declarations with no typechecker errors, 1 pretty printer errors: [\n", "")

    def run_main(self, cl, nd):
        outputs = {"con-leche": cl, "nanoda": nd}  # what ext.run returns, by step label
        saved = {k: getattr(ext, k) for k in ("build_tools", "run", "timed_scan", "run_controls",
                                              "run_attribute_controls", "attribute_scan")}
        with tempfile.TemporaryDirectory() as d:
            open(os.path.join(d, "pm.ndjson"), "w").close()
            os.mkdir(os.path.join(d, "logs"))
            ext.build_tools = lambda work, mirror, logs: {n: "tool" for n in ext.TOOLS}
            ext.run = lambda label, cmd, **kw: outputs.get(label, (0, "", ""))
            ext.timed_scan = lambda label, export, logs: (True, dict(self.REP))
            ext.run_controls = lambda bins, work, jobs, logs: (True, [])
            ext.run_attribute_controls = lambda work, logs: (True, [])
            ext.attribute_scan = lambda *a: (True, {"declarations": 1, "attributed": [], "excludedCount": 0})
            argv, sys.argv = sys.argv, ["external_checkers.py", "--work", d, "--nanoda-upstream", "skip"]
            try:
                with contextlib.redirect_stdout(io.StringIO()) as out:
                    try:
                        ext.main()
                        code = 0
                    except SystemExit as e:
                        code = e.code
            finally:
                sys.argv = argv
                for k, v in saved.items():
                    setattr(ext, k, v)
        return code, out.getvalue()

    def test_agreeing_counts_pass(self):
        code, out = self.run_main(self.CL_OK, self.ND_OK)
        self.assertIn(code, (0, None), out)

    def test_con_leche_wrong_count(self):
        for n in (0, 167602, 167604):
            code, out = self.run_main((0, f"con-leche: accepted {n} declarations (--verified)\n", ""), self.ND_OK)
            self.assertEqual(code, 1, out)
            self.assertIn("con-leche count", out)

    def test_nanoda_wrong_count(self):
        for n in (0, 175577, 167603):
            code, out = self.run_main(self.CL_OK, (0, f"Checked {n} declarations with no typechecker errors\n", ""))
            self.assertEqual(code, 1, out)
            self.assertIn("nanoda count", out)

    def test_con_leche_crash(self):
        # killed by a signal after printing its success line, and with no output at all
        for result in ((-11, self.CL_OK[1], ""), (-9, "", ""), (1, "", "con-leche: uncaught exception")):
            code, out = self.run_main(result, self.ND_OK)
            self.assertEqual(code, 1, out)
            self.assertIn("FAILED: con-leche", out)

    def test_nanoda_crash(self):
        for result in ((101, self.ND_OK[1], "thread panicked"), (-11, "", ""), (0, "", "")):
            code, out = self.run_main(self.CL_OK, result)
            self.assertEqual(code, 1, out)
            self.assertIn("FAILED: nanoda", out)


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
        self.assertEqual({ext.show(n) for n in ext.CORE_AXIOMS}, set(SEVEN))
        self.assertEqual(ext.TRUST_COMPILER_USERS, {ext.N("Lean", "reduceBool"), ext.N("Lean", "reduceNat")})

    def test_a_control_for_each_rule(self):
        reasons = {c[4] for c in ext.CONTROLS}
        self.assertEqual(reasons, {"axiom", "sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat",
                                   "Lean.trustCompiler"})
        both = {c[0]: c[3] for c in ext.CONTROLS}
        for module in ("NegSorry", "NegAxiom"):
            self.assertEqual(both[module], {"con-leche", "nanoda", "scan"})
        for module, _, theorem, rejectors, _ in ext.CONTROLS:
            self.assertIn("scan", rejectors, module)

    def test_quoted_name_controls(self):
        """The two lookalikes, each a one-component name printed like core's two-component one."""
        by_module = {c[0]: c for c in ext.CONTROLS}
        axiom, user = by_module["NegQuotedAxiom"], by_module["NegQuotedCoreUser"]
        self.assertIn("axiom «Classical.choice» : False", axiom[1])
        self.assertEqual((axiom[3], axiom[4]), ({"con-leche", "scan"}, "axiom"))
        self.assertIn("opaque «Lean.reduceBool» : True := Lean.trustCompiler", user[1])
        self.assertEqual((user[3], user[4]), ({"scan"}, "Lean.trustCompiler"))

    def test_attribute_controls(self):
        sources = " ".join(c[1] for c in ext.ATTRIBUTE_CONTROLS)
        self.assertIn("@[implemented_by ", sources)
        self.assertIn("@[extern ", sources)
        self.assertEqual(ext.REPO_PREFIXES, ["PM", "Checks"])
        lean = (ROOT / "scripts" / "implementation_attributes.lean").read_text(encoding="utf-8")
        self.assertIn("Compiler.getImplementedBy? env c", lean)
        self.assertIn("isExtern env c", lean)


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

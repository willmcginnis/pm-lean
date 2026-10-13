"""Counterparts (docs/NAMING.md): a recorded counterpart must state PM's formula, as its declaration's own
type says, not only as the record says.

Each mutation below records a false match, keeping the recorded formulas as they were. It must be caught
by the `counterparts` rule of scripts/export_names.py (the signature read strictly) and, for a Lean core
counterpart, by Lean (Checks/Counterparts.lean as the mutated record would generate it); and the unmutated
records must pass both.
"""
import copy
import importlib.util
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT, run

spec = importlib.util.spec_from_file_location("export_names", ROOT / "scripts" / "export_names.py")
export_names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(export_names)


def record(ctx, pm):
    return next(r for r in ctx["counterparts"]["counterparts"] if r["pm"] == pm)


def or_inl_for_or_inr(ctx):
    # ✱1·3 is q ⊃ p ∨ q, Or.inr; Or.inl (p → p ∨ q) is a real declaration with its real signature and
    # line, but not ✱1·3. The recorded formulas stay as they were.
    r = record(ctx, "*1.3")
    r.update(declaration="Or.inl", signature="∀ {a b : Prop}, a → a ∨ b", source="src/Init/Prelude.lean:622")


def signature_not_a_type(ctx):
    record(ctx, "*1.3")["signature"] = "NOT A LEAN TYPE"


def iff_swapped_unflagged(ctx):
    # Classical.not_not states ¬¬a ↔ a; ✱4·13 is p ≡ ∼∼p. Drop the record's flag (and restate its
    # statement to match), so only the declaration's type can tell.
    r = record(ctx, "*4.13")
    r.update(iff_reversed=False, iff_reversed_at=[], statement="(p ↔ ¬¬p)")


def specialized_unflagged(ctx):
    # id is {α : Sort u} → α → α; ✱2·08 needs it at Prop, which the record must say
    record(ctx, "*2.08")["specialized"] = False


def instantiation_identifies(ctx):
    # two of Or.symm's variables instantiated with one of PM's: never allowed
    record(ctx, "*1.4")["instantiation"] = ["p", "p"]


MUTATIONS = [or_inl_for_or_inr, signature_not_a_type, iff_swapped_unflagged, specialized_unflagged,
             instantiation_identifies]


def context():
    ctx = export_names.context()
    ctx["counterparts"] = copy.deepcopy(ctx["counterparts"])
    return ctx


def entries():
    return json.loads((ROOT / "data" / "export_names.json").read_text(encoding="utf-8"))


def lean(text):
    """(exit code, output) of Lean on `text` as a file, with the repository's toolchain."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", encoding="utf-8", delete=False) as f:
        f.write(text)
    try:
        return run(["lake", "env", "lean", f.name])
    finally:
        os.unlink(f.name)


class TestCounterparts(unittest.TestCase):
    def test_unmutated_pass(self):
        es, ctx = entries(), context()
        self.assertEqual(export_names.check_counterparts(es, ctx), [])
        code, out = run(["lake", "env", "lean", "Checks/Counterparts.lean"])
        self.assertEqual(code, 0, out)
        self.assertIn("counterparts: 54 checked by Lean", out)

    def test_generated_file_is_the_committed_one(self):
        es, ctx = entries(), context()
        self.assertEqual(export_names.counterparts_lean(es, ctx),
                         (ROOT / "Checks" / "Counterparts.lean").read_text(encoding="utf-8"))

    def test_python_catches_each_mutation_and_its_revert_passes(self):
        es = entries()
        for mutate in MUTATIONS:
            with self.subTest(mutation=mutate.__name__):
                ctx = context()
                mutate(ctx)
                self.assertTrue(export_names.check_counterparts(es, ctx), f"{mutate.__name__} passed")
                self.assertEqual(export_names.check_counterparts(es, context()), [])

    def test_lean_catches_each_mutation(self):
        es = entries()
        for mutate in MUTATIONS:
            with self.subTest(mutation=mutate.__name__):
                ctx = context()
                mutate(ctx)
                code, out = lean(export_names.counterparts_lean(es, ctx))
                self.assertNotEqual(code, 0, f"Lean accepted {mutate.__name__}:\n{out}")
                self.assertIn("error", out)
        # reverted: the same records as committed pass again
        code, out = lean(export_names.counterparts_lean(es, context()))
        self.assertEqual(code, 0, out)

    def test_lean_messages(self):
        es = entries()
        for mutate, says in ((or_inl_for_or_inr, "instantiated, it states"),
                             (signature_not_a_type, "not the recorded signature"),
                             (iff_swapped_unflagged, "instantiated, it states"),
                             (specialized_unflagged, "the record does not say so"),
                             (instantiation_identifies, "the same variable")):
            with self.subTest(mutation=mutate.__name__):
                ctx = context()
                mutate(ctx)
                self.assertIn(says, lean(export_names.counterparts_lean(es, ctx))[1])

    def test_lean_does_not_unfold(self):
        # `#counterpart` compares types exactly (but for A → False as ¬A): a declaration whose type only
        # unfolds to the schema fails, as the criterion requires; the kernel's `example` alone would pass it
        head = export_names.LEAN_CHECK_HEAD + "\nvariable (p q : Prop)\n"
        ok = head + ('def myImp (a b : Prop) : Prop := a → b\n'
                     'theorem t1 {a b : Prop} : myImp (a ∧ b) a := And.left\n'
                     'example : ((p ∧ q) → p) := @t1 p q\n')
        self.assertEqual(lean(ok)[0], 0, lean(ok)[1])
        code, out = lean(ok + '#counterpart t1 [p, q] "∀ {a b : Prop}, myImp (a ∧ b) a" : ((p ∧ q) → p)\n')
        self.assertNotEqual(code, 0, out)
        not_false = head + ('theorem t2 {a : Prop} : a → (a → False) → False := fun h k => k h\n'
                            '#counterpart t2 [p] "∀ {a : Prop}, a → (a → False) → False" : (p → ¬¬p)\n')
        self.assertEqual(lean(not_false)[0], 0, lean(not_false)[1])

    def test_signature_reader(self):
        f = export_names.parse_signature
        self.assertEqual(f("∀ {a b : Prop}, b → a ∨ b"), ([("a", "Prop"), ("b", "Prop")], ("→", "b", ("∨", "a", "b"))))
        self.assertEqual(f("theorem not_imp_not : ¬a → ¬b ↔ b → a", "variable {a b : Prop}")[1],
                         ("↔", ("→", ("¬", "a"), ("¬", "b")), ("→", "b", "a")))
        self.assertEqual(f("{α : Sort u} → α → α"), ([("α", "Sort")], ("→", "α", "α")))
        self.assertEqual(f("∀ {b c : Prop} {α : Sort u_1}, (∀ (a : α), b ∧ c) ↔ (∀ (a : α), b) ∧ ∀ (a : α), c")[1],
                         ("↔", ("→", "α", ("∧", "b", "c")), ("∧", ("→", "α", "b"), ("→", "α", "c"))))
        self.assertEqual(f("∀ {a : Prop}, (a → False) → a")[1], ("→", ("¬", "a"), "a"))
        for bad in ("NOT A LEAN TYPE", "∀ {a b : Prop}, a → c", "∀ {a : Nat}, a", "∀ {a b : Prop}, a ↔ b ↔ a",
                    "∀ {a : Prop}, a = a", "∀ {a : Prop}, a →", "∀ (a : Prop) (h : a), a",
                    "theorem t : a → a"):
            with self.subTest(signature=bad), self.assertRaises(ValueError):
                f(bad)

    def test_source_header_must_be_the_signature(self):
        # --verify-counterparts on a stand-in checkout of the pinned Mathlib file: the declaration's header
        # (to :=) and its section's `variable` line must be the recorded ones
        ctx = context()
        r = record(ctx, "*4.1")
        ctx["counterparts"]["counterparts"] = [r]
        path, line = r["source"].rsplit(":", 1)
        vline = int(r["section_variables_source"].rsplit(":", 1)[1])

        def verify(header, variables="variable {a b : Prop}"):
            with tempfile.TemporaryDirectory() as d:
                f = pathlib.Path(d) / f"mathlib4-{r['commit']}" / path
                f.parent.mkdir(parents=True)
                lines = ["-- filler"] * (int(line) + 2)
                lines[vline - 1] = variables
                lines[int(line) - 1] = header
                f.write_text("\n".join(lines) + "\n", encoding="utf-8")
                return export_names.verify_counterparts(ctx, d)

        self.assertEqual(verify("theorem not_imp_not : ¬a → ¬b ↔ b → a := proof"), [])
        self.assertEqual(verify("theorem   not_imp_not :\n ¬a → ¬b ↔ b → a :=\n proof"), [])
        self.assertTrue(verify("theorem not_imp_not : ¬a → ¬b ↔ a → b := proof"))
        self.assertTrue(verify("theorem not_imp_not : ¬a → ¬b ↔ b → a := proof", "variable {b a : Prop}"))

    def test_every_lean_core_counterpart_is_checked_by_lean(self):
        cps = context()["counterparts"]["counterparts"]
        self.assertEqual({r["checked"] for r in cps if r["repository"] == "lean4"}, {"lean"})
        text = (ROOT / "Checks" / "Counterparts.lean").read_text(encoding="utf-8")
        self.assertEqual(text.count("\n#counterpart "), sum(r["repository"] == "lean4" for r in cps))

    def test_at_the_pinned_lean(self):
        # the pins are the platform's Lean; run the same check with it when it is installed
        version = context()["counterparts"]["repositories"]["lean4"]["version"]
        toolchain = f"leanprover/lean4:{version}"
        try:
            listed = subprocess.run(["elan", "toolchain", "list"], capture_output=True, text=True).stdout
        except FileNotFoundError:
            self.skipTest("no elan")
        if toolchain not in listed:
            self.skipTest(f"{toolchain} is not installed")
        code, out = run(["elan", "run", toolchain, "lean", "Checks/Counterparts.lean"])
        self.assertEqual(code, 0, out)
        self.assertIn("counterparts: 54 checked by Lean", out)


if __name__ == "__main__":
    unittest.main()

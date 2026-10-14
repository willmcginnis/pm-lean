"""docs/TYPES_DESIGN.md's table of files ("What was built") gives each file's length in lines.

A release review found `PM/Star23.lean` listed with 838 lines after the file had grown to 850: the
table is written by hand, and nothing compared it with the files. This test does: each count in the
Lines column equals the number of lines of the file named in the same position of the File column."""
import re
import unittest

from common import ROOT

DOC = ROOT / "docs" / "TYPES_DESIGN.md"
HEADER = "| File | Lines | Contents |"


def table_rows():
    """(line number, files, counts) for each row of the table."""
    lines = DOC.read_text(encoding="utf-8").split("\n")
    start = lines.index(HEADER)
    rows = []
    for i in range(start + 2, len(lines)):
        if not lines[i].startswith("|"):
            break
        cells = [c.strip() for c in lines[i].split("|")[1:-1]]
        files = re.findall(r"`([^`]+\.lean)`", cells[0])
        counts = [int(n) for n in re.findall(r"\d+", cells[1])]
        rows.append((i + 1, files, counts))
    return rows


def line_count(path):
    return len(path.read_text(encoding="utf-8").splitlines())


class TestTypesDesignLines(unittest.TestCase):
    def test_table_is_found(self):
        self.assertGreater(len(table_rows()), 10, "the table of files was not found")

    def test_counts_are_the_files(self):
        for lineno, files, counts in table_rows():
            with self.subTest(line=lineno):
                self.assertTrue(files, f"TYPES_DESIGN.md:{lineno} names no .lean file")
                self.assertEqual(len(files), len(counts),
                                 f"TYPES_DESIGN.md:{lineno}: {len(files)} files but {len(counts)} counts")
                for f, n in zip(files, counts):
                    path = ROOT / f
                    self.assertTrue(path.is_file(), f"TYPES_DESIGN.md:{lineno}: {f} does not exist")
                    self.assertEqual(line_count(path), n,
                                     f"TYPES_DESIGN.md:{lineno}: {f} has {line_count(path)} lines, the table says {n}")


if __name__ == "__main__":
    unittest.main()

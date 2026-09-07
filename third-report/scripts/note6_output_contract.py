"""Frozen presentation contract for the 12 tables of the reviewed note.

This is deliberately independent of costs.py. Never auto-update the fixture in a
packaging/test run. A new mathematical example needs a separately reviewed fixture.
The comparison tolerates round-off in the two unrounded floating-point heights,
not changes in any exact row or symbolic expression. This is NOT a proof oracle.
"""
from __future__ import annotations
import difflib
import json
import math
from pathlib import Path

FLOAT_LINES = (
    "      height with the correct ideal gcd : ",
    "      height after cancelling norms     : ",
)

def check_output(table: int, actual: str) -> None:
    expected = json.loads(Path(__file__).with_name("note6_output_fixture.json").read_text())[str(table)]
    # These lines were printed with repr(float), which can differ in the last bit
    # across compliant platforms. Allow only a 1e-10 absolute numerical tolerance.
    normalized = []
    exp_lines = expected.splitlines(keepends=True)
    act_lines = actual.splitlines(keepends=True)
    for line in act_lines:
        for prefix in FLOAT_LINES:
            if line.startswith(prefix):
                candidates = [x for x in exp_lines if x.startswith(prefix)]
                if len(candidates) != 1:
                    raise AssertionError("ambiguous frozen height line")
                want = candidates[0]
                value, reference = float(line[len(prefix):]), float(want[len(prefix):])
                if not (math.isfinite(value) and abs(value-reference) < 1e-10):
                    raise AssertionError("absolute height differs from the reviewed fixture")
                line = want
                break
        normalized.append(line)
    normalized_text = "".join(normalized)
    if normalized_text != expected:
        diff = "".join(difflib.unified_diff(expected.splitlines(True),
                       normalized_text.splitlines(True), fromfile="reviewed fixture",
                       tofile="actual output"))
        raise AssertionError(f"Table {table} violates its fixed-paper output contract:\n{diff}")

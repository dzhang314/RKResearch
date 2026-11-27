#!/usr/bin/env python3
"""Verify that the portable exact coefficient export matches the solved tableau."""
from fractions import Fraction
from pathlib import Path
import importlib.util
import json
import sys

base = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("dirk10_real", base / "check-dirk10-real-algebraic.py")
model = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = model
spec.loader.exec_module(model)
doc = json.loads((base / "dirk-order10-eleven-real-coefficients.json").read_text())

def read(encoded, algebra=None):
    if algebra is None:
        n, d = map(int, encoded)
        assert d > 0
        return Fraction(n, d)
    assert len(encoded) == len(algebra.mod) - 1
    return model.ev([algebra.cast(read(x, algebra.base)) for x in encoded], algebra.gen)

for key, alg in [("mod_k", model.K), ("mod_r8", model.T), ("mod_r9", model.V)]:
    assert tuple(read(x, alg.base) for x in doc[key]) == alg.mod

clocks, b, g, h, G = model.polynomials_on_layout()
A = model.solve_tableau(clocks, b, g, h, G)
alg = model.V
assert [read(x, alg) for x in doc["nodes"]] == clocks
assert [read(x, alg) for x in doc["weights"]] == b
assert [[read(x, alg) for x in row] for row in doc["matrix_lower_triangular"]] == A
residual, inverse = [read(x, alg) for x in doc["star11_residual"]]
assert residual == 11 * sum(weight * c**10 for weight, c in zip(b, clocks)) - 1
assert residual * inverse == alg.one
print("Exact export matches every literal tap, clock, weight and the eleventh-star unit certificate.")

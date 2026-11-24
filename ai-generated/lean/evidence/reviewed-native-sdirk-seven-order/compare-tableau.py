#!/usr/bin/env python3
"""Compare the actual Lean source data with the earlier sealed exact tableau.

Usage: python3 compare-tableau.py SDIRKNineReplayData.lean tableau.json
This is a provenance check. The Lean proof independently checks arithmetic.
"""
from fractions import Fraction
from pathlib import Path
import json
import re
import sys

lean, archive = map(Path, sys.argv[1:])
text = lean.read_text()
arch = json.loads(archive.read_text())

def integer(name):
    match = re.search(r"^def " + name + r" : ℤ := (-?\d+)$", text, re.M)
    return int(match[1])

def coefficients(raw):
    return [int(s) for s in raw.split(",") if s.strip()]

def bracketed(name, prefix):
    match = re.search(
        r"^def " + name + r" : " + prefix + r"\[([-\d,\s]+)\]", text, re.M
    )
    return coefficients(match[1])

def limb(src):
    src = src.strip()
    if src.startswith("("):
        assert src.endswith(")")
        src = src[1:-1]
    if src.startswith(".atom"):
        m = re.fullmatch(r"\.atom \[([-\d,\s]*)\]", src)
        return coefficients(m[1])
    m = re.fullmatch(
        r"\.mul \(\.atom \[(-?\d+)\]\) \(\.atom \[([-\d,\s]*)\]\)", src
    )
    return [int(m[1]) * c for c in coefficients(m[2])]

def split_top_level(src):
    nesting = 0
    i0 = None
    for i, c in enumerate(src):
        if c in "([":
            nesting += 1
        elif c in ")]":
            nesting -= 1
        elif c == "," and nesting == 0:
            assert i0 is None
            i0 = i
    assert nesting == 0 and i0 is not None
    return src[:i0], src[i0+1:]

def pair(raw):
    raw = raw.strip()
    if raw == "QExpr.zero":
        return ([], [])
    assert raw.startswith("⟨") and raw.endswith("⟩")
    return tuple(limb(p) for p in split_top_level(raw[1:-1]))

def scale(data, n, d=1):
    out = [Fraction(int(c) * n, int(data["den"]) * d) for c in data["numAscending"]]
    assert all(q.denominator == 1 for q in out)
    return [q.numerator for q in out]

def scaled_pair(data, n):
    return (
        scale(data["constant"], n),
        scale(data["timesSmallerNode"], n, dy),
    )

da, db, dy = map(integer, ["stageDen", "weightDen", "shapeDen"])
assert da > 0 and db > 0 and dy > 0
assert bracketed("innerMod", r"List ℤ := ") == list(map(int, arch["tPolynomialAscending"]))
assert bracketed("outerU", r"Expr := \.atom ") == scale(arch["U"], dy)
assert bracketed("outerV", r"Expr := \.atom ") == scale(arch["V"], dy**2)

stage_case = text.split("def rawA ")[1].split("def rawB ")[0]
assert "if i=j then QExpr.const (4*stageDen) else" in stage_case
assert re.search(r"^    \| _,_ => QExpr.zero$", stage_case, re.M)
stages = {}
for i, j, p in re.findall(r"^    \| (\d+), (\d+) => (.*?)(?=^    \|)", stage_case, re.M | re.S):
    key = (int(i), int(j))
    assert 0 <= key[1] < key[0] < 9 and key not in stages
    stages[key] = pair(p)
assert len(arch["A0"]) == 9 and all(len(row) == 9 for row in arch["A0"])
for i in range(9):
    for j in range(9):
        got = ([4 * da], []) if i == j else stages.get((i, j), ([], []))
        assert got == scaled_pair(arch["A0"][i][j], 4 * da), (i, j)

weight_case = text.split("def rawB ")[1].split("/-- Values are interpreted")[0]
assert re.search(r"^  \| _ => QExpr.zero$", weight_case, re.M)
weights = {}
for i, p in re.findall(r"^  \| (\d+) => (.*?)(?=^  \|)", weight_case, re.M | re.S):
    assert 0 <= int(i) < 9 and int(i) not in weights
    weights[int(i)] = pair(p)
assert len(arch["b"]) == 9
for i in range(9):
    assert weights.get(i, ([], [])) == scaled_pair(arch["b"][i], db), i

print("All 81 stage entries and all 9 weights match the sealed exact tableau.")
print("Both quadratic coefficients and the monic degree-12 relation match after integer normalization.")

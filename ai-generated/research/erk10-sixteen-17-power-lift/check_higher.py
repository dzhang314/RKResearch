#!/usr/bin/env python3
"""Independently verify the prime-power literals, without the constructor."""
from functools import cache
from math import gcd, prod
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / "erk10-sixteen-f17"
sys.path.insert(0, str(BASE))
from rooted import trees, tf

seed = json.loads((BASE / "tableau.json").read_bytes())
previous_modulus = 17
previous_A = [tuple(map(int, row)) for row in seed["A"]]
previous_b = tuple(map(int, seed["b"]))
for k in range(2, 6):
    data = json.loads((HERE / "literals" / f"mod17pow{k}.json").read_bytes())
    m = data["modulus"]
    A = [tuple(map(int, row)) for row in data["A"]]
    b = tuple(map(int, data["b"]))
    assert data["prime"] == 17 and data["exponent"] == k and m == 17**k
    assert len(A) == len(b) == 16
    assert all(len(row) == i for i, row in enumerate(A))
    assert all(0 <= a < m for row in A for a in row) and all(0 <= a < m for a in b)
    assert [tuple(x % previous_modulus for x in r) for r in A] == previous_A
    assert tuple(x % previous_modulus for x in b) == previous_b

    def dot(x, y):
        return sum(v*w for v,w in zip(x,y)) % m

    @cache
    def stage(t):
        child = [incoming(u) for u in t]
        return tuple(prod(r[i] for r in child) % m for i in range(16))

    @cache
    def incoming(t):
        return tuple(dot(row, stage(t)) for row in A)

    ns = []
    for d in range(1, 11):
        ts = trees(d)
        assert len(set(ts)) == len(ts)
        for t in ts:
            assert tf(t) * dot(b, stage(t)) % m == 1, (k, d, t)
        ns.append(len(ts))
    assert ns == [1, 1, 2, 4, 9, 20, 48, 115, 286, 719]
    defect = (11 * dot(b, stage(((),)*10)) - 1) % m
    assert defect == int(data["bush_failure"]) and defect % 17 == 2 and gcd(defect,m) == 1
    print(k, m, sum(ns), defect, "compatible")
    previous_modulus, previous_A, previous_b = m, A, b

#!/usr/bin/env python3
"""Verify the retuned dense prefix and its storage in the final literal."""
from functools import cache
from math import prod
from pathlib import Path
import json
from rooted import trees, tf

here = Path(__file__).resolve().parent
prefix = json.loads((here / "prefix.json").read_bytes())
literal = json.loads((here / "tableau.json").read_bytes())
p = prefix["p"]
A = prefix["A"]
P = prefix["Pi"]
assert p == literal["field"] == 17
assert [len(row) for row in A] == list(range(8))
assert [len(row) for row in P] == [8] * 5

def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % p

@cache
def stage(t):
    children = [incoming(u) for u in t]
    return tuple(prod(row[i] for row in children) % p for i in range(8))

@cache
def incoming(t):
    return tuple(dot(row, stage(t)) for row in A)

def rank(rows):
    M = [list(row) for row in rows]
    r = 0
    for j in range(len(M[0])):
        i = next((i for i in range(r, len(M)) if M[i][j] % p), None)
        if i is None:
            continue
        M[r], M[i] = M[i], M[r]
        inv = pow(M[r][j] % p, -1, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(r+1, len(M)):
            q = M[i][j] % p
            M[i] = [(x - q * y) % p for x, y in zip(M[i], M[r])]
        r += 1
    return r

count = 0
for n in range(1, 6):
    for t in trees(n):
        assert [dot(row, stage(t)) for row in P] == [
            n * pow(tf(t), -1, p) % p if j == n-1 else 0 for j in range(5)
        ]
        count += 1
assert count == 17
rows = [[(-dot(row, stage(t))) % p for row in P] + [6 * pow(tf(t), -1, p) % p] for t in trees(6)]
H6 = prefix["H6"]
assert len(rows) == 20 and rank(rows) == rank(H6) == rank(rows + H6) == prefix["rank"] == 3
theta = sum(A[-1]) % p
assert theta == 10
primitive = [sum(P[j][i] * pow(theta, j+1, p) * pow(j+1, -1, p)
                 for j in range(5)) % p for i in range(8)]
assert primitive == A[-1] + [0]
A16 = [list(map(int, row)) for row in literal["A"]]
alias = int(literal["reverse_c"][-1])
scale = alias * pow(theta, -1, p)
assert alias == 14
assert [[scale * t % p for t in row] for row in A] == A16[:8]
assert [sum(row) % p for row in A16[7:]][::-1] == list(map(int, literal["reverse_c"]))
print("Dense order five:",count,"exact rooted polynomial identities.")
print("Size-six residual rank:",rank(rows),"; all",len(rows),"profiles checked.")
print("Integrated decoder equals literal endpoint at",theta,"; scaled endpoint",alias,"present exactly.")

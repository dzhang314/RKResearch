#!/usr/bin/env python3
"""Exact independent rooted-tree check of the archived F17 tableau."""
from functools import cache
from hashlib import sha256
from math import prod
from pathlib import Path
import json

LITERAL = Path(__file__).with_name("tableau.json")
assert sha256(LITERAL.read_bytes()).hexdigest() == "02a8c0ca3e5b11e9c851b237420d46ce798ea14fb727dc2e00e51b85fd1cedf9"
D = json.loads(LITERAL.read_bytes())
p = D["field"]
assert p == 17
A = [tuple(map(int, row)) for row in D["A"]]
b = tuple(map(int, D["b"]))
assert len(A) == len(b) == 15 and all(len(r) == i for i, r in enumerate(A))
assert all(0 <= t < p for r in A for t in r) and all(0 <= t < p for t in b)

def dot(x, y):
    return sum(a * b for a, b in zip(x, y)) % p

def act(z):
    return tuple(dot(row, z) for row in A)

def order(u):
    return 1 + sum(map(order, u))

@cache
def forests(n, lower):
    if n == 0:
        return ((),)
    out = []
    for d in range(order(lower), n+1):
        for t in trees(d):
            if order(t) == order(lower) and t < lower:
                continue
            out.extend((t,) + f for f in forests(n-d, t))
    return tuple(out)

@cache
def trees(n):
    return forests(n-1, ())

@cache
def density(t):
    return order(t) * prod(map(density, t))

@cache
def incoming(t):
    return act(stage(t))

@cache
def stage(t):
    children = list(map(incoming, t))
    return tuple(prod(c[i] for c in children) % p for i in range(15))

counts = []
for m in range(1, 11):
    ts = trees(m)
    assert len(ts) == len(set(ts))
    for t in ts:
        assert density(t) * dot(b, stage(t)) % p == 1, (m, t)
    counts.append(len(ts))
assert counts == [1, 1, 2, 4, 9, 20, 48, 115, 286, 719]
assert sum(counts) == 1205
star = ((),) * 10
value = dot(b, stage(star))
defect = (11 * value - 1) % p
assert defect == int(D["next_failure_value"]) == 8
print("15 stages, strictly explicit over F17")
print("1,205 rooted-tree identities verified, with counts:", counts)
print("size-11 star: weighted value", value, "normalized defect", defect)

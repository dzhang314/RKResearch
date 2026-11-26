"""Replay the 41-stage explicit tableau with integer arithmetic, then test exact order."""

import json
from fractions import Fraction
from functools import cache
from math import lcm, prod
from pathlib import Path


def paid_remainder(n):
    n = abs(n)
    for prime in (2, 3, 5, 7, 11, 13):
        while n and n % prime == 0:
            n //= prime
    return n


data = json.loads(Path(__file__).with_name("tableau-13-41.json").read_text())
A = [tuple(map(Fraction, row)) for row in data["A"]]
b = tuple(map(Fraction, data["b"]))
s = 41
assert len(A) == len(b) == s
assert all(len(row) >= i and not any(row[i:]) for i, row in enumerate(A))
assert len({row[:i] + (0,) * (s - i) for i, row in enumerate(A)}) == s
D = lcm(*(v.denominator for row in A for v in row), *(v.denominator for v in b))
assert paid_remainder(D) == 1

# Scaling A by D scales the weight vector of a size-n tree by D**(n-1).
scaled_A = [
    tuple((j, int(D * value)) for j, value in enumerate(row) if value)
    for row in A
]
scaled_b = tuple(int(D * value) for value in b)


@cache
def forests(n, lower=(0, ())):
    if n == 0:
        return ((),)
    return tuple(
        (branch,) + tail
        for k in range(max(1, lower[0]), n + 1)
        for branch in trees(k)
        if (k, branch) >= lower
        for tail in forests(n - k, (k, branch))
    )


@cache
def trees(n):
    return forests(n - 1)


@cache
def size(t):
    return 1 + sum(map(size, t))


@cache
def factorial(t):
    return size(t) * prod(map(factorial, t))


@cache
def weighted(t):
    branches = tuple(extension(child) for child in t)
    return tuple(prod(branch[i] for branch in branches) for i in range(s))


@cache
def extension(t):
    v = weighted(t)
    return tuple(sum(a * v[j] for j, a in row) for row in scaled_A)


def defect_numerator(t):
    return factorial(t) * sum(a * v for a, v in zip(scaled_b, weighted(t))) - D**size(t)


counts = (1, 1, 2, 4, 9, 20, 48, 115, 286, 719, 1842, 4766, 12486)
for n, expected in enumerate(counts, 1):
    ts = trees(n)
    assert len(ts) == expected
    assert all(defect_numerator(t) == 0 for t in ts), n
    print(f"Order {n}: checked {expected} rooted trees")

t = ((), ((),) * 11)
B = ((),) * 13
assert size(t) == size(B) == 14
dt = Fraction(defect_numerator(t), D**14 * factorial(t))
dB = Fraction(defect_numerator(B), D**14 * factorial(B))
eta = -dt - dB/2
assert paid_remainder(eta.numerator) == paid_remainder(eta.denominator) == 1
assert (-1 / eta) * dt + (-1 / (2 * eta)) * dB == 1
print(f"Next-order defects (without tree factorials): {dt}, {dB}; eta = {eta}")
print(f"Verified {sum(counts)} rooted conditions and a unit-ideal order-14 obstruction")

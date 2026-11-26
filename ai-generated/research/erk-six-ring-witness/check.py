"""Check every rooted equation through order six over the rationals."""
from fractions import Fraction as F
from functools import lru_cache
from math import prod

A = tuple(tuple(map(F, row)) for row in (
    (),
    ("1/3",),
    (0, "2/3"),
    ("1/12", "1/3", "-1/12"),
    ("-1/16", "9/8", "-3/16", "-3/8"),
    (0, "9/8", "-3/8", "-3/4", "1/2"),
    ("-1/2", "3/2", 0, 0, 0, 0),
    ("29/4", -24, "63/4", 18, 0, -16, 0),
))
b = tuple(map(F, ("11/120", 0, "27/40", "27/40", "-4/15", "-4/15", "1/12", "1/120")))

@lru_cache(None)
def forest(n, lower=None):
    if n == 0:
        return ((),)
    return tuple(
        (t,) + rest
        for j in range(1, n + 1) for t in trees(j)
        if lower is None or lower <= t
        for rest in forest(n - j, t)
    )

@lru_cache(None)
def trees(n):
    return forest(n - 1)

@lru_cache(None)
def size(t):
    return 1 + sum(map(size, t))

@lru_cache(None)
def factorial(t):
    return size(t) * prod(map(factorial, t))

@lru_cache(None)
def phi(t):
    return tuple(
        prod(sum(x * w for x, w in zip(row, phi(child))) for child in t)
        for row in A
    )

def read(t):
    return sum(x * w for x, w in zip(b, phi(t)))

for x in (*b, *(x for row in A for x in row)):
    d = x.denominator
    for prime in (2, 3, 5):
        while d % prime == 0:
            d //= prime
    assert d == 1

for n, expected in enumerate((1, 1, 2, 4, 9, 20), start=1):
    ts = trees(n)
    assert len(ts) == len(set(ts)) == expected
    assert all(factorial(t) * read(t) == 1 for t in ts)
    print(f"order {n}: {len(ts)} exact conditions")
tall = ()
for _ in range(6):
    tall = (tall,)
assert read(tall) == F(-1, 2160)
assert factorial(tall) * read(tall) - 1 == F(-10, 3)
print("order seven tall-tree defect: -10/3")

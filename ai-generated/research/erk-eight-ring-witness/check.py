"""Exact replay of the rooted-tree order of a Shanks tableau and its adaptation."""
from fractions import Fraction
from functools import lru_cache
from math import prod


def row(denominator, *numerators):
    return tuple(Fraction(n, denominator) for n in numerators)


original_A = (
    (),
    row(9, 1),
    row(24, 1, 3),
    row(16, 1, 0, 3),
    row(500, 29, 0, 33, -12),
    row(972, 33, 0, 0, 4, 125),
    row(36, -21, 0, 0, 76, 125, -162),
    row(243, -30, 0, 0, -32, 125, 0, 99),
    row(324, 1175, 0, 0, -3456, -6250, 8424, 242, -27),
    row(324, 293, 0, 0, -852, -1375, 1836, -118, 162, 324),
    row(1620, 1303, 0, 0, -4260, -6875, 9990, 1030, 0, 0, 162),
    row(4428, -8595, 0, 0, 30720, 48750, -66096, 378, -729, -1944, -1296, 3240),
)
original_b = row(840, 41, 0, 0, 0, 0, 216, 272, 27, 27, 36, 180, 41)
a = original_A[-1]
r = row(8, 0, 0, 0, 0, 0, 3, 2, 0, 0, 3, 0)
adapted_A = original_A[:-1] + (r, tuple(41*e-40*f for e,f in zip(a,r))+(0,))
adapted_b = row(840, 41, 0, 0, 0, 0, 216, 272, 27, 27, 36, 180, 40, 1)
assert adapted_A[-1] == row(108, -8595, 0, 0, 30720, 48750, -67716, -702, -729, -1944, -2916, 3240, 0)
assert all(len(q)==i for i,q in enumerate(adapted_A))

for x in (*adapted_b, *(x for q in adapted_A for x in q)):
    d = x.denominator
    for prime in (2, 3, 5, 7):
        while d % prime == 0:
            d //= prime
    assert d == 1


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
def phi(A, t):
    return tuple(
        prod(sum(x * w for x, w in zip(q, phi(A, child))) for child in t)
        for q in A
    )


def read(A, b, t):
    return sum(x * w for x, w in zip(b, phi(A, t)))


c = tuple(sum(q) for q in original_A)
donors = (5, 6, 9)
assert tuple(c[i] for i in donors) == row(6, 1, 3, 5)

for n in range(1,5):
    for t in trees(n):
        stage = phi(original_A,t)
        for i in donors:
            assert stage[i] == Fraction(n, factorial(t))*c[i]**(n-1)
        assert sum(x*w for x,w in zip(a,stage)) == sum(x*w for x,w in zip(r,stage)) == Fraction(1,factorial(t))

for n,expected in enumerate((1,1,2,4,9,20,48,115,286),start=1):
    ts=trees(n)
    assert len(ts)==len(set(ts))==expected
    for t in ts:
        v=read(adapted_A,adapted_b,t)
        assert v==read(original_A,original_b,t)
        if n<=8:
            assert factorial(t)*v==1
    print(f"order {n}: {len(ts)} original and adapted reads agree")

witness = ((),)*8
assert size(witness)==9 and factorial(witness)==9
assert read(adapted_A, adapted_b, witness)==Fraction(4321,38880)
assert factorial(witness)*read(adapted_A,adapted_b,witness)-1==Fraction(1,4320)
print("order nine cleared bush defect: 1/4320")

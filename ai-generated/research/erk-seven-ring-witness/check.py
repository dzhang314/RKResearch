"""Exact replay of the rooted-tree order of a Shanks tableau and its adaptation."""
from fractions import Fraction
from functools import lru_cache
from math import prod


def row(denominator, *numerators):
    return tuple(Fraction(n, denominator) for n in numerators)


original_A = (
    (),
    row(27, 4),
    row(18, 1, 3),
    row(12, 1, 0, 3),
    row(8, 1, 0, 0, 3),
    row(54, 13, 0, -27, 42, 8),
    row(4320, 389, 0, -54, 966, -824, 243),
    row(20, -231, 0, 81, -1164, 656, -122, 800),
    row(288, -127, 0, 18, -678, 456, -9, 576, 4),
    row(820, 1481, 0, -81, 7104, -3376, 72, -5040, -60, 720),
)
original_b = row(840, 41, 0, 0, 27, 272, 27, 216, 0, 216, 41)
a = original_A[-1]
r = original_A[7] + (0, 0)
adapted_A = original_A[:-1] + (tuple(41 * e - 40 * f for e, f in zip(a, r)),)
adapted_b = row(840, 41, 0, 0, 27, 272, 27, 216, 40, 216, 1)
assert adapted_A[-1] == row(20, 10721, 0, -3321, 53664, -29616, 4952, -37040, -60, 720)
assert all(len(q) == i for i, q in enumerate(adapted_A))

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


for n in range(1, 4):
    for t in trees(n):
        assert sum(x * w for x, w in zip(a, phi(original_A, t))) == sum(
            x * w for x, w in zip(r, phi(original_A, t))
        )

for n, expected in enumerate((1, 1, 2, 4, 9, 20, 48, 115), start=1):
    ts = trees(n)
    assert len(ts) == len(set(ts)) == expected
    for t in ts:
        v = read(adapted_A, adapted_b, t)
        assert v == read(original_A, original_b, t)
        if n <= 7:
            assert factorial(t) * v == 1
    print(f"order {n}: {len(ts)} original and adapted reads agree")

witness = ((), (), (), ((), (), ()))
assert size(witness) == 8 and factorial(witness) == 32
assert read(adapted_A, adapted_b, witness) == Fraction(809, 25920)
assert factorial(witness) * read(adapted_A, adapted_b, witness) - 1 == Fraction(-1, 810)
print("order eight cleared branching defect: -1/810")

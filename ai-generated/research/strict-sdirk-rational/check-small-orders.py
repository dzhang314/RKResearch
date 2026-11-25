"""Check all rooted-tree conditions and the two finite-field obstructions."""
from fractions import Fraction
from itertools import combinations_with_replacement
from math import prod

trees = {1: [()]}
for n in range(2, 6):
    children = [(k, t) for k in range(1, n) for t in trees[k]]
    trees[n] = [
        tuple(t for _, t in word)
        for j in range(1, n)
        for word in combinations_with_replacement(children, j)
        if sum(k for k, _ in word) == n - 1
    ]
assert [len(trees[n]) for n in range(1, 6)] == [1, 1, 2, 4, 9]


def order(t):
    return 1 + sum(map(order, t))


def factorial(t):
    return order(t) * prod(map(factorial, t))


def weights(a, t):
    descendants = [weights(a, child) for child in t]
    return [prod(sum(x * y for x, y in zip(row, v)) for v in descendants)
            for row in a]


fixtures = [
    (((3, 0, 0), (6, 3, 0), (8, 4, 3)), (3, 2, 3), Fraction(5, 108)),
    (((3, 0, 0, 0), (6, 3, 0, 0), (12, -6, 3, 0), (6, 4, 2, 3)),
     (3, 1, 1, 3), Fraction(11, 1296)),
]
values = [[8], [72], [432, 864], [1944, 3888, 5832, 11664]]
for a, b, witness in fixtures:
    p = len(b)
    assert all(a[i][i] == 3 for i in range(p))
    assert all(a[i][j] == 0 for i in range(p) for j in range(i + 1, p))
    assert all(w > 0 for w in b)

    def step(t):
        return sum(x * y for x, y in zip(weights(a, t), b))

    for n in range(1, p + 1):
        assert sorted(step(t) for t in trees[n]) == values[n - 1]
        assert all(factorial(t) * step(t) == 8 * 18 ** (n - 1)
                   for t in trees[n])
    tall = ()
    for _ in range(p):
        tall = (tall,)
    assert Fraction(step(tall), 8 * 18 ** p) == witness
    assert witness * factorial(tall) != 1

for a, expected in [
    ((1, -6, 6), [1, 1, 3, 2, 3]),
    ((-1, 12, -36, 24), [4, 4, 1, 4, 2]),
]:
    residues = [sum(c * r ** j for j, c in enumerate(a)) % 5 for r in range(5)]
    assert a[-1] % 5 and residues == expected and all(residues)

print("Rational order-three/four tableaux and modulo-five obstructions verified.")

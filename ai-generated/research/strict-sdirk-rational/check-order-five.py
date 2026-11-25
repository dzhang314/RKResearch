"""Exact rooted-tree replay of the order-five rational SDIRK witness."""
from fractions import Fraction as Q
from functools import cache
from itertools import combinations_with_replacement, product
from math import prod

rows = [
    (1,),
    (-1, 1),
    (0, -1, 1),
    (Q(-9, 50), Q(-31, 50), 0, 1),
    (Q(-4, 9), Q(1, 9), 0, 0, 1),
    (Q(-1, 2), Q(1, 2), 0, 0, 0, 1),
    (Q(7, 2), Q(-3, 10), Q(2, 5), 2, Q(-18, 5), -2, 1),
    (6, 9, -1, Q(-60, 7), Q(-45, 7), Q(5, 2), Q(-5, 2), 1),
]
A = [r + (0,) * (8 - len(r)) for r in rows]
b = (0, 0, Q(1, 48), Q(125, 336), Q(27, 56), Q(5, 96), Q(5, 96), Q(1, 48))
assert all(A[i][i] == 1 and all(x == 0 for x in A[i][i+1:]) for i in range(8))

@cache
def order(t):
    return 1 + sum(map(order, t))

@cache
def factorial(t):
    return order(t) * prod(map(factorial, t))

@cache
def phi(t):
    vs = [phi(u) for u in t]
    return tuple(prod(sum(a * x for a, x in zip(row, v)) for v in vs) for row in A)

def mass(t):
    return sum(w*x for w, x in zip(b, phi(t)))

trees = {1: [()]}
for n in range(2, 7):
    pool = [t for k in range(1, n) for t in trees[k]]
    trees[n] = [word for arity in range(1, n)
                for word in combinations_with_replacement(pool, arity)
                if sum(map(order, word)) == n-1]
    assert len(trees[n]) == len(set(trees[n]))
assert [len(trees[n]) for n in range(1, 7)] == [1, 1, 2, 4, 9, 20]
for n in range(1, 6):
    assert all(factorial(t)*mass(t) == 1 for t in trees[n])
assert all(factorial(t)*mass(t) != 1 for t in trees[6])
tall = ()
for _ in range(5):
    tall = (tall,)
assert mass(tall) == Q(-5, 24)

# Sharp rational four-site quadrature, and the witness's reflected quadrature.
x = (Q(0), Q(1, 3), Q(4, 5), Q(1))
w = (Q(5, 48), Q(27, 56), Q(125, 336), Q(1, 24))
for j in range(5):
    assert sum(wi*xi**j for wi, xi in zip(w, x)) == Q(1, j+1)
clocks = tuple(map(sum, A))
weighted_clocks = {xi:sum(wi for i, wi in enumerate(b) if clocks[i] == xi)
                   for xi in set(clocks)}
assert weighted_clocks == dict(zip((1-xi for xi in x), w))
for n, d in product(range(3), repeat=2):
    if (n, d) != (0, 0):
        assert (25*n**4 - 22*n*n*d*d + 5*d**4) % 3 == (2 if d else 1)
print("17 paid rooted trees exact; 20 order-six failures; four-site quadrature and eight modulo-three residues verified.")

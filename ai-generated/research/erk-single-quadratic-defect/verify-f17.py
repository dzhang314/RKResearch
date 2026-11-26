"""Verify the order, support, and pure rank of the six-stage F_17 example."""

from functools import cache
from math import prod

P = 17
A = ((), (6,), (0, 12), (7, 3, 14), (4, 0, 16, 4), (1, 5, 13, 6, 10))
b = (5, 0, 2, 8, 16, 4)
one = (1,) * len(b)


@cache
def forests(n, lower=(0, ())):
    if n == 0:
        return ((),)
    return tuple(
        (t,) + tail
        for k in range(max(1, lower[0]), n + 1)
        for t in forests(k - 1)
        if (k, t) >= lower
        for tail in forests(n - k, (k, t))
    )


@cache
def size(t):
    return 1 + sum(map(size, t))


@cache
def tree_factorial(t):
    return size(t) * prod(map(tree_factorial, t))


def dot(u, v):
    return sum(x*y for x, y in zip(u, v)) % P


def act(v):
    return tuple(dot(row, v) for row in A)


@cache
def phi(t):
    children = [act(phi(u)) for u in t]
    return tuple(prod(v[i] for v in children) % P for i in range(len(b)))


def defect(t):
    return (tree_factorial(t)*dot(b, phi(t))-1) % P


def rank(vectors):
    pivots = {}
    for v in vectors:
        r = list(v)
        for i in range(len(b)):
            if not r[i]:
                continue
            if i in pivots:
                r = [(x-r[i]*y) % P for x, y in zip(r, pivots[i])]
            else:
                pivots[i] = [x*pow(r[i], -1, P) % P for x in r]
                break
    return len(pivots)


def pure(t):
    n = size(t)
    inverse = pow(tree_factorial(t), -1, P)
    return [(z-n*inverse*pow(x, n-1, P)) % P for z, x in zip(phi(t), c)]


trees = [forests(n-1) for n in range(1, 7)]
assert list(map(len, trees)) == [1, 1, 2, 4, 9, 20]
assert all(defect(t) == 0 for grade in trees[:5] for t in grade)
assert any(defect(t) for t in trees[5])
c = act(one)
assert tuple((2*y-x*x) % P for x, y in zip(c, act(c))) == (0, 15, 0, 0, 0, 0)
assert rank(pure(t) for grade in trees[:5] for t in grade) == 3
print("F17: exact order five, one quadratic defect, pure rank three.")

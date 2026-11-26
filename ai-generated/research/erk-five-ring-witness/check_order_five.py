"""Exact replay of the six-stage tableau."""
from fractions import Fraction as F
from functools import cache
from math import prod

A = ((), (F(1, 2),), (F(1, 4), F(1, 4)),
     (F(2, 9), 0, F(1, 9)),
     (F(-5, 18), F(-5, 36), 0, F(5, 4)),
     (F(27, 5), 2, -1, -9, F(18, 5)))
b = (F(8, 75), 0, F(1, 15), F(9, 20), F(9, 25), F(1, 60))


@cache
def trees(n):
    """A tree is a sorted tuple of its children, with leaf ()."""
    if n == 1:
        return ((),)
    candidates = tuple(sorted((t, k) for k in range(1, n) for t in trees(k)))

    def forests(total, first):
        if total == 0:
            yield ()
        for i in range(first, len(candidates)):
            child, size = candidates[i]
            if size <= total:
                for rest in forests(total - size, i):
                    yield (child,) + rest

    return tuple(forests(n - 1, 0))


@cache
def size(t):
    return 1 + sum(map(size, t))


@cache
def factorial(t):
    return size(t) * prod(map(factorial, t))


@cache
def stages(t):
    return tuple(prod(sum(a * child_j for a, child_j in zip(row, stages(u)))
                      for u in t)
                 for row in A)


def weight(t):
    return sum(w * v for w, v in zip(b, stages(t)))


if __name__ == "__main__":
    counts = []
    for n in range(1, 6):
        labels = trees(n)
        assert len(labels) == len(set(labels))
        for t in labels:
            assert factorial(t) * weight(t) == 1, (n, t, weight(t))
        counts.append(len(labels))
    assert counts == [1, 1, 2, 4, 9]
    tall = ()
    for _ in range(5):
        tall = (tall,)
    assert weight(tall) == F(1, 960)
    assert factorial(tall) * weight(tall) - 1 == F(-1, 4)
    print("All", sum(counts), "order conditions through order five pass.")
    print("Six-vertex chain: weight 1/960, cleared defect -1/4.")

#!/usr/bin/env python3
"""Independent exact complete rooted order replay for the literal DIRK tableau."""

from collections import Counter
from functools import cache
from math import prod

P = 419
A = (
    (0,),
    (1, 1),
    (411, 151, 69),
    (405, 211, 166, 275),
    (346, 22, 202, 78, 0),
    (197, 92, 337, 333, 199, 153),
    (308, 277, 195, 389, 238, 318, 0),
    (404, 51, 42, 44, 384, 40, 201, 129),
    (124, 51, 119, 264, 352, 107, 317, 287, 119),
    (397, 6, 32, 44, 405, 1, 302, 387, 44, 299),
    (22, 0, 48, 39, 60, 293, 26, 38, 403, 329, 0),
)
B = (357, 0, 76, 25, 2, 154, 52, 37, 321, 220, 14)


@cache
def ordered(n):
    """All root-attach words with n vertices, with separate orders of siblings."""
    if n < 2:
        return ((),) if n == 1 else ()
    return tuple((a, b) for j in range(1, n)
                 for a in ordered(j) for b in ordered(n-j))


@cache
def canonical(tree):
    """Sort the immediate branches after recursive normalization."""
    if not tree:
        return ()
    a, b = tree
    return tuple(sorted(canonical(a) + (canonical(b),)))


@cache
def vertex_count(t):
    return 1 + sum(vertex_count(s) for s in t)


@cache
def factorial(t):
    return vertex_count(t) * prod(factorial(s) for s in t)


@cache
def elementary(t):
    # A forest of immediate child trees, so the empty forest is the leaf.
    arcs = [elementary(s) for s in t]
    return tuple(prod(sum(aij * vj for aij, vj in zip(ai, v)) % P for v in arcs) % P
                 for ai in A)


assert len(A) == len(B) == 11
assert all(len(row) == i+1 for i, row in enumerate(A))
assert all(P % d for d in range(2, 21)) and 21*21 > P
assert [i+1 for i, row in enumerate(A) if row[-1] == 0] == [1, 5, 7, 11]
counts = Counter()
for n in range(1, 11):
    trees = {canonical(t) for t in ordered(n)}
    for tree in trees:
        assert vertex_count(tree) == n
        out = sum(w*v for w, v in zip(B, elementary(tree))) % P
        assert factorial(tree)*out % P == 1, (n, tree, out)
        counts[n] += 1
assert list(counts.values()) == [1, 1, 2, 4, 9, 20, 48, 115, 286, 719]
assert sum(counts.values()) == 1205
c = tuple(sum(row) % P for row in A)
assert c == (0, 2, 212, 219, 229, 54, 49, 38, 64, 241, 1)
g = tuple((sum(aij * xj**2 for aij, xj in zip(row, c))
           - x**3 * pow(3, -1, P)) % P for row, x in zip(A, c))
assert [i + 1 for i, d in enumerate(g) if d] == [2] and B[1] == 0
moment = sum(w * x**10 for w, x in zip(B, c)) % P
assert moment == 224 and pow(11, -1, P) == 381
assert 11*moment % P == 369  # The denominator-cleared 11-vertex star.
print(f'F{P}: {sum(counts.values())}/1205 unordered rooted conditions through order 10')
print('ordered attach-word counts:', [len(ordered(n)) for n in range(1, 11)])
print('11-vertex star: degree-ten moment 224; expected 381 (cleared 369 ≠ 1)')

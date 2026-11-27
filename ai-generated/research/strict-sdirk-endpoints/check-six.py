"""Exact independent rooted-tree replay of the three new finite-field tableaux."""
from functools import cache
from itertools import combinations_with_replacement
import json
from math import isqrt, prod
from pathlib import Path

@cache
def size(tree):
    return 1 + sum(size(child) for child in tree)

@cache
def factorial(tree):
    return size(tree) * prod(factorial(child) for child in tree)

def trees_by_size(n):
    layers = [[()]]
    for k in range(2, n + 1):
        older = [tree for group in layers for tree in group]
        # Use sequences of child IDs in nondecreasing order: all and only
        # unordered rooted trees, with total child size k-1.
        def children(start, remaining):
            if remaining == 0:
                yield ()
            for j in range(start, len(older)):
                child = older[j]
                if size(child) > remaining:
                    break
                for tail in children(j, remaining - size(child)):
                    yield (child,) + tail
        layers.append(list(children(0, k - 1)))
    return layers

def check(q, A, b, layers):
    assert q >= 2 and all(q % d for d in range(2, isqrt(q) + 1))
    assert len(A) == len(b) == 6 and all(len(row) == i+1 for i,row in enumerate(A))
    assert 0 < A[0][0] < q and all(row[-1] == A[0][0] for row in A)
    assert all(0 <= x < q for row in A for x in row) and all(0 <= x < q for x in b)

    @cache
    def stage(tree):
        x = [1] * 6
        for child in tree:
            y = stage(child)
            x = [f * sum(a * yj for a,yj in zip(row,y)) % q for f,row in zip(x,A)]
        return tuple(x)

    def payment(tree):
        return factorial(tree) * sum(bi * v for bi,v in zip(b,stage(tree))) % q

    for group in layers[:6]:
        for tree in group:
            assert payment(tree) == 1, (q, tree)
    values = [sum(row)%q for row in A]
    assert len(set(values)) == 6
    seventh_bush = ((),) * 6
    assert seventh_bush in layers[6]
    failure = payment(seventh_bush)
    assert failure == {263: 161, 457: 43, 126963077: 4126301}[q]
    print(f"F_{q}: gamma={A[0][0]}, 37/37 through six; seventh bush={failure} != 1")

if __name__ == "__main__":
    all_trees = trees_by_size(7)
    assert list(map(len, all_trees)) == [1, 1, 2, 4, 9, 20, 48]
    data = json.loads(Path(__file__).with_name("six-stage-witnesses.json").read_text())
    assert set(data) == {"263", "457", "126963077"}
    for q, t in data.items():
        check(int(q), t["A"], t["b"], all_trees)

"""Check the 25-stage tableau against every rooted-tree condition through order 12."""
from fractions import Fraction
from functools import cache
from math import factorial, lcm, prod
from pathlib import Path
import json
import sys


def main(directory):
    tableau = json.loads((directory / "tableau-12-factorial-25.json").read_text())
    receipt = json.loads((directory / "receipt-12-factorial-25.json").read_text())
    order, stages = 12, 25
    rows = [list(map(Fraction, row)) for row in tableau["A"]]
    weights = list(map(Fraction, tableau["b"]))
    assert len(weights) == len(rows) == stages
    assert all(len(row) == i for i, row in enumerate(rows))
    d = lcm(*(x.denominator for row in rows for x in row))
    e = lcm(*(x.denominator for x in weights))
    assert factorial(order) ** 2 % d == factorial(order) % e == 0
    matrix = [[int(d * x) for x in row] for row in rows]
    b = [int(e * x) for x in weights]

    # Trees are tuples of children in nondecreasing order under (size, tuple).
    # The empty tuple is the one-vertex tree.
    @cache
    def size(t):
        return 1 + sum(map(size, t))

    def key(t):
        return (size(t), t)

    @cache
    def forest(n, minimum=()):
        if n == 0:
            return ((),)
        return tuple(
            (t,) + tail
            for k in range(size(minimum), n + 1)
            for t in trees(k)
            if key(t) >= key(minimum)
            for tail in forest(n - k, t)
        )

    @cache
    def trees(n):
        return forest(n - 1)

    @cache
    def tree_factorial(t):
        return size(t) * prod(map(tree_factorial, t))

    @cache
    def integrated_weight(t):
        # The input vector is the Butcher weight vector times d^(size(t)-1).
        child_vectors = [integrated_weight(u) for u in t]
        v = [prod(entries) for entries in zip(*child_vectors)] if t else [1] * stages
        return tuple(sum(a * x for a, x in zip(row, v)) for row in matrix)

    def defect(t):
        child_vectors = [integrated_weight(u) for u in t]
        v = [prod(entries) for entries in zip(*child_vectors)] if t else [1] * stages
        return Fraction(tree_factorial(t) * sum(w * x for w, x in zip(b, v)),
                        e * d ** (size(t) - 1)) - 1

    counts = []
    for n in range(1, order + 1):
        bucket = trees(n)
        counts.append(len(bucket))
        for t in bucket:
            assert defect(t) == 0, (n, t)
    assert counts == [1, 1, 2, 4, 9, 20, 48, 115, 286, 719, 1842, 4766]

    def from_json(t):
        return tuple(sorted(map(from_json, t), key=key))

    defects = []
    for tree, expected in receipt["next"]["literal_witness"]:
        t = from_json(tree)
        assert size(t) == order + 1
        value = defect(t)
        assert value == Fraction(expected)
        defects.append(value)
    assert len(defects) == 2
    assert sum(k * delta for k, delta in zip((-513216000, 191600640), defects)) == 1
    print(f"Verified {sum(counts)} rooted-tree conditions and an integer blend "
          "of two order-13 defects equal to one.")
    print("The denominators of A and b divide (12!)² and 12!, respectively.")


if __name__ == "__main__":
    main(Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent)

"""Replay the two local order-20 decoder claims on every required rooted tree."""

from functools import cache
from math import factorial, prod
from hashlib import sha256
import json

import construct as rk


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


def verify_chart(grade, reverse, seed, rational_grid=False):
    a, operations, readers = rk.long(grade, reverse, seed,
                                      reflected_twenty=not (reverse and rational_grid),
                                      symmetric_last=reverse and rational_grid)
    assert len(a) == (34 if reverse and not rational_grid else 27)
    assert all(len(row) <= i for i, row in enumerate(a))
    assert all(rk.paid_integer(x.denominator) for row in a + readers for x in row)
    # The read matrix is invertible over Z[1/20!], not just over Q.
    _, determinant = rk.read(operations, readers, rk.eval_at(rk.Z))
    assert rk.unit(determinant)

    @cache
    def stage_vector(t):
        child_columns = [
            [rk.dot(row, stage_vector(child)) for row in a] for child in t
        ]
        return [prod(col[i] for col in child_columns) for i in range(len(a))]

    count = 0
    for n in range(1, grade + 1):
        for t in forests(n - 1):
            v = stage_vector(t)
            for op, row in zip(operations, readers):
                assert rk.dot(row, v) == rk.F(n, tree_factorial(t)) * op(n - 1)
            count += 1
    print(f"grade {grade}, {len(a)} rows: all {count} tree columns pass every read")


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rational-grid', action='store_true')
    args = parser.parse_args()
    p, grade = (19, 9) if args.rational_grid else (20, 10)
    rk.PAID = factorial(p)
    raw = (rk.HERE.parent / 'erk-eleven-twelve-moment-splice' / 'paid9-seed.json').read_bytes()
    assert sha256(raw).hexdigest() == rk.SEED_SHA256
    seed = json.loads(raw)
    verify_chart(9, False, seed, rational_grid=args.rational_grid)
    verify_chart(grade, True, seed, rational_grid=args.rational_grid)
    tableau = 'tableau-19-rational.json' if args.rational_grid else 'tableau-20.json'
    assert rk.construct(p, seed, rational_grid=args.rational_grid) == (rk.HERE / tableau).read_text()

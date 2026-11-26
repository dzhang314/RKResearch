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


def verify_chart(grade, reverse, seed):
    a, operations, readers = rk.long(grade, reverse, seed, reflected_twenty=True)
    assert len(a) == (34 if reverse else 27)
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
    rk.PAID = factorial(20)
    raw = (rk.HERE.parent / 'erk-eleven-twelve-moment-splice' / 'paid9-seed.json').read_bytes()
    assert sha256(raw).hexdigest() == rk.SEED_SHA256
    seed = json.loads(raw)
    verify_chart(9, False, seed)
    verify_chart(10, True, seed)
    assert rk.construct(20, seed) == (rk.HERE / 'tableau-20.json').read_text()

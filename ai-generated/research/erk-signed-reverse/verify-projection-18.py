"""Check all finite forward/reverse chart conditions for the order-18 projection."""

from fractions import Fraction as F
from functools import cache
from math import comb, factorial, prod
from pathlib import Path
from hashlib import sha256
import json
import sys

sys.dont_write_bytecode = True

import construct as family


@cache
def forests(n, lower=(0, ())):
    if n == 0:
        return ((),)
    return tuple(
        (branch,) + tail
        for k in range(max(1, lower[0]), n + 1)
        for branch in trees(k)
        if (k, branch) >= lower
        for tail in forests(n-k, (k, branch))
    )


@cache
def trees(n):
    return forests(n - 1)


@cache
def size(t):
    return 1 + sum(map(size, t))


@cache
def tree_factorial(t):
    return size(t) * prod(map(tree_factorial, t))


def derivative_columns(A):
    sparse = [tuple((j, a) for j, a in enumerate(row) if a) for row in A]

    @cache
    def derivative(t):
        children = tuple(extension(branch) for branch in t)
        return tuple(prod(v[i] for v in children) for i in range(len(A)))

    @cache
    def extension(t):
        v = derivative(t)
        return tuple(sum(a * v[j] for j, a in row) for row in sparse)

    return derivative


def polynomial_after_substitution(coefficients, shift, scale):
    return [
        sum(coefficients[i] * comb(i, j) * shift**(i-j) * scale**j
            for i in range(j, len(coefficients)))
        for j in range(len(coefficients))
    ]


def check(A, operators, rows, reverse):
    coeff_rows = [family.read(operators, rows, lambda j: F(j == i))[0]
                  for i in range(8)]
    assert all(family.paid_integer(value.denominator)
               for row in A + coeff_rows for value in row)
    derivative = derivative_columns(A)
    inner = [-1, -48, 35, 480, -155, -816, 153]
    q_centered = [x-y for x,y in zip(inner+[0,0], [0,0]+inner)]
    q = polynomial_after_substitution(q_centered, -1, 2)
    reflected_q = polynomial_after_substitution(q_centered, 1, -2)
    assert family.unit(F(q[-1]))
    tested = 0
    for n in range(1, 10):
        for t in trees(n):
            v = derivative(t)
            polynomial = [family.dot(row, v) for row in coeff_rows] + [F(0)]
            exact = [F(0)] * 9
            exact[n-1] = F(n, tree_factorial(t))
            difference = [a - b for a,b in zip(exact, polynomial)]
            if n <= 8:
                assert not any(difference), (reverse, t)
            elif reverse:
                factor = difference[-1] / q[-1]
                assert difference == [factor * x for x in q], t
            else:
                # Primitive of the difference paired with q(1−2x).
                integral = sum(a*b/F((i+1)*(i+j+2))
                               for i,a in enumerate(difference)
                               for j,b in enumerate(reflected_q) if a and b)
                assert integral == 0, t
            tested += 1
    assert tested == 486
    print(("reverse" if reverse else "forward") + f" chart: all {tested} conditions pass")


family.PAID = factorial(18)
seed_path = Path(__file__).parent.parent / "erk-eleven-twelve-moment-splice" / "paid9-seed.json"
seed_bytes = seed_path.read_bytes()
assert sha256(seed_bytes).hexdigest() == family.SEED_SHA256
seed = json.loads(seed_bytes)
check(*family.long(8, False, seed, projected=True), reverse=False)
check(*family.long(9, True, seed, projected=True), reverse=True)

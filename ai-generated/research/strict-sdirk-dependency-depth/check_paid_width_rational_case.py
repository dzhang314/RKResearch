"""Exact seven-stage p=4 example; no search or external dependency."""
from fractions import Fraction as Q
from math import prod

A = [[Q(int(i == j)) for j in range(7)] for i in range(7)]
B = [[Q(0) for j in range(7)] for i in range(7)]
strict = {
    (1, 0): Q(1, 4),
    (2, 1): Q(-2), (3, 1): Q(-3, 10),
    (4, 2): Q(-317, 1088), (4, 3): Q(-635, 1088),
    (5, 2): Q(1, 68), (5, 3): Q(-35, 68),
    (6, 2): Q(259, 1088), (6, 3): Q(-395, 1088),
}
for (i, j), v in strict.items():
    A[i][j] = B[i][j] = v
b = [Q(0)] * 4 + [Q(8, 27), Q(11, 27), Q(8, 27)]

def action(M, v):
    return [sum(a * z for a, z in zip(row, v)) for row in M]

def column(M, t):
    children = [action(M, column(M, u)) for u in t]
    return [prod(c[i] for c in children) for i in range(7)]

def output(M, t):
    return sum(a * z for a, z in zip(b, column(M, t)))

def order(t):
    return 1 + sum(order(u) for u in t)

def factorial(t):
    return order(t) * prod(factorial(u) for u in t)

leaf = ()
tall2 = (leaf,)
tall3 = (tall2,)
tall4 = (tall3,)
bush3 = (leaf, leaf)
trees = [leaf, tall2, bush3, tall3, (leaf, leaf, leaf),
         (tall2, leaf), (bush3,), tall4]
assert action(A, [Q(1)] * 7) == [Q(1), Q(5, 4), Q(-1), Q(7, 10),
    Q(1, 8), Q(1, 2), Q(7, 8)]
vals = [output(A, t) for t in trees]
assert vals == [Q(1, factorial(t)) for t in trees]
assert output(A, (leaf,) * 4) == Q(51, 256) != Q(1, 5)
assert output(B, tall4) == Q(1, 24)
assert 1 + sum(range(2, 10)) + 10 * 10 == 145 == (20 * 10 - 45 - 2) - 8
print("paid tree outputs:", ", ".join(map(str, vals)))
print("first bush failure:", output(A, (leaf,) * 4), "instead of", Q(1, 5))
print("strict height-three tall readout:", output(B, tall4))
print("order-20 stage count under the conditional construction: 145")

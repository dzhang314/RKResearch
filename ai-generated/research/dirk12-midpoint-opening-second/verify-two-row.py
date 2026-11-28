#!/usr/bin/env python3
"""Independent cleared polynomial replay, using only the standard library."""
from fractions import Fraction as Q
from math import comb

def plus(a, b):
    k = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0) for i in range(k)]

def mul(a, b):
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c

def powp(a, k):
    c = [1]
    for _ in range(k):
        c = mul(c, a)
    return c

def sc(a, k):
    return [r*k for r in a]

def zero(p):
    assert not any(p), p

x = [0, 1]
one_less = [-1, 1]
Db = [1, -5, 5]
rn = mul(powp(x, 3), [-20, 55, -49, 15])
kn = sc(mul(powp(x, 3), powp(one_less, 3)), -30)
eps = sc([2, -7, 7], Q(-1, 1260))
l0 = sc(mul(mul(powp(x, 3), one_less), [2, -6, 5]), Q(1, 2))
l1 = sc(mul(mul(x, one_less), [-1, 2]), Q(1, 2))
for j in range(1, 6):
    rhs = plus(sc(plus(mul(Db, powp(x, j+1)), sc(rn, -1)), Q(1, j+1)),
               sc(kn, Q(-1, j+2)))
    if j == 5:
        rhs = plus(rhs, mul(kn, eps))
    zero(plus(plus(l0, mul(l1, powp(x, j))), sc(rhs, -1)))
    print("exact cleared two-point entering degree", j)

def half_leg_prime(j):
    return [Q(k*(-1)**(j-k)*comb(j,k)*comb(j+k,k), 2**(k-1)) for k in range(1, j+1)]

p0 = mul(x, plus(half_leg_prime(5), sc(half_leg_prime(7), Q(6, 7))))
q0 = mul(x, half_leg_prime(6))
zero(plus(p0, sc(mul(one_less, q0), Q(-13, 7))))
print("exact centered Legendre determinant factor")
p = [Q(1, 4), Q(1, 3), Q(8, 11), Q(1)]
ell = [Q(256, 945), Q(81, 520), Q(161051, 393120), Q(89, 1080)]
h = [Q(1, 384), Q(-1, 162), Q(4, 3993), Q(-1, 534)]
assert sum(l*z**6 for l, z in zip(ell, p)) - Q(1, 7) == Q(5, 11088)
assert sum(l*g*z**3 for l, g, z in zip(ell, h, p)) == Q(-1, 47520)
print("unpaid ghost excess 5/11088 and third lifted tap −1/47520")

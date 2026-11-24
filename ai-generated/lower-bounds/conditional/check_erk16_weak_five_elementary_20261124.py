"""Replay the exact scalar identities in the weak-five elementary exclusions."""

from fractions import Fraction as Q
from math import factorial


def add(f, g):
    h = [Q(0)] * max(len(f), len(g))
    for p in (f, g):
        for i, c in enumerate(p):
            h[i] += c
    return h


def mul(*polys):
    h = [Q(1)]
    for f in polys:
        g = [Q(0)] * (len(f) + len(h) - 1)
        for i, c in enumerate(h):
            for j, d in enumerate(f):
                g[i+j] += c*d
        h = g
    return h


def derivative(f):
    return [i*c for i, c in enumerate(f) if i]


def integral(f, u=1):
    return sum(c*u**(i+1)/Q(i+1) for i, c in enumerate(f))


def linear(a):
    return [-a, Q(1)]


def centered_moment(j):
    return Q(1, 2**(2*j+1)*(2*j+1)*(2*j+3))


x = [Q(0), Q(1)]
t = linear(Q(1, 2))
u = Q(5, 6)
quadratic = [Q(5, 24), Q(-1), Q(1)]
assert integral(mul(x, quadratic), u) == integral(mul(x, x, quadratic), u) == 0
F = mul([Q(1, 5)], x, x, linear(u), linear(u), linear(Q(5, 8)))
assert derivative(F) == mul(x, linear(u), quadratic)

s_factors = mul(x, [Q(5, 24), Q(-1)], [Q(5, 36), Q(-1)], [Q(15, 64), Q(-1)])
quadratic_test = sum(c*Q(factorial(i)**2, factorial(2*i+1)) for i, c in enumerate(s_factors))
assert quadratic_test == Q(233, 11612160)

u = Q(5, 8)
cubic = mul(t, add(mul(t, t), [Q(-3, 32)]))
assert integral(mul(x, cubic), u) == integral(mul(x, x, cubic), u) == 0
F = mul([Q(1, 6)], x, x, linear(u), linear(u), [Q(3, 8), Q(-13, 10), Q(1)])
assert derivative(F) == mul(x, linear(u), cubic)


def A(j):
    return centered_moment(j+2) - Q(7, 64)*centered_moment(j+1) + Q(3, 2048)*centered_moment(j)


a1, a2, a3 = map(A, (1, 2, 3))
assert (a1, a2, a3) == (Q(199, 5160960), Q(1697, 227082240), Q(3397, 2361655296))
assert a1*a3 - a2*a2 == Q(-10723, 27931769516851200)
assert a1 > 0 and a2/a1 > Q(1, 100)

# h=1-a gives Z=t^2+p. For a=(13-sqrt(19))/20,
# (a-1/2)^2=(14-3 sqrt(19))/200, strictly less than 1/100.
assert 4**2 < 19 < 5**2
print("Exact quadratic and reflection-odd exclusions and cubic diagnostic: pass")

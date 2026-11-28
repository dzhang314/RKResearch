#!/usr/bin/env python3
"""Recompute the actual tap determinants and degree-preserving residue tests."""
from math import prod
from sympy import QQ, factor
from sympy.polys.fields import field

F, a, t = field("a,t", QQ)
O, I = F.zero, F.one
b = (3 - 5 * a) / (5 - 10 * a)
s = 2 * t - 1
mini = (I, t, s)
P = (4000000, -40800000, 167610000, -371374000, 514995300, -489665160,
     338552340, -175445532, 68020317, -19036726, 3582327, -399522, 19705)
J = (66, -132, 84, -18, 1)


def horner(coeffs, x):
    r = 0
    for u in coeffs:
        r = r * x + u
    return r


def H(x):
    return x * (2 * x - 1) * horner(J, x)


def root_polynomial(nodes):
    f = [I]
    for e in nodes:
        f = [-e * f[0]] + [u - e * v for u, v in zip(f, f[1:])] + [f[-1]]
    return f


def integrate(coeffs, top):
    return sum(v * top**(i+1) / (i+1) for i, v in enumerate(coeffs))


def tap(nodes, j, top):
    x = nodes[j]
    others = nodes[:j]+nodes[j+1:]
    return integrate(root_polynomial(others), top) / prod(x-v for v in others)


def determinant(m, c, d):
    return m[0]*(c[1]*d[2]-c[2]*d[1]) + m[1]*(c[2]*d[0]-c[0]*d[2]) + m[2]*(c[0]*d[1]-c[1]*d[0])


assert not integrate(root_polynomial((O, a, b, I)), I)
M = [-integrate(root_polynomial((O, a, b, I, v)), v) for v in mini]
C = [tap((O, a, b, I, v), 1, v) for v in mini]
D = [tap((O, a, b, I, v), 2, v) for v in mini]
assert C[0] == tap((O, a, b, I), 1, I)
assert D[0] == tap((O, a, b, I), 2, I)
N3, N4 = (O, a/2, a), (O, a/2, a, b)
S = [sum(x**4*tap(N,j,z) for j,x in enumerate(N))-z**5/5
     for N,z in zip((N3, N4), (a, b), strict=True)]
A2d3low = tap((O, a/4, a/2), 1, a/2)*a**3/384
T = [tap(N, 1, z)*A2d3low for N,z in zip((N3, N4), (a, b), strict=True)]
U, V = 10*a*a-10*a+3, 10*a*a-15*a+6
E1 = -a**5*(5*a-3)**3*U**3/(54000000*(2*a-1)**5*V)
assert S[0]*T[1]-S[1]*T[0] == E1
E2 = -125*t**3*(2*a-1)**4*(t-1)**7*(2*t-1)**3*(-5*a*a+6*a*t+a-3*t+1) / (
    18*a*(t-a)*(a-1)*(5*a-3)*(5*a-2)*(2*t-a-1)*U
    *(10*a*t-5*a-5*t+3)*(20*a*t-15*a-10*t+8))
assert determinant(M, C, D) == E2
tt = (5*a*a-a-1)/(6*a-3)
specialize = lambda x: factor(x.as_expr().subs(t.as_expr(), tt.as_expr()))
rank_two = 125*(5*a*a-a-1)**3/(1944*a*(2*a-1)*(5*a-3)*U)
assert specialize(C[0]*D[1]-C[1]*D[0]) == factor(rank_two.as_expr())
Jac = [H(v/(4*t)) for v in mini]
E3 = -125*(a-1)*(5*a-2)*(10*a*a-8*a+1)*horner(P,a)/(
    2239488*a*(2*a-1)**3*(4*a-1)*(5*a-3)*(10*a-7)*(5*a*a-a-1)**2*U)
assert specialize(determinant(C, D, Jac)) == factor(E3.as_expr())
h = list(map(F,(0,-1,20,-120,300,-330,132)))
assert H(a) == horner(h[::-1],a)
for j in range(6):
    assert integrate([O]*j+h,I) == I/42
rp, rj = [horner(P,j)%11 for j in range(11)], [horner(J,j)%13 for j in range(13)]
assert P[0]%11 and J[0]%13 and all(rp) and all(rj)
print("actual low size-six, mini scalar/cubic and Jacobi determinants: exact")
print("Jacobi weighted moments and rank-two minor: exact")
print("degree-12 numerator / mod11:",rp)
print("Jacobi quartic / mod13:",rj)
print("all scoped arithmetic gates passed")

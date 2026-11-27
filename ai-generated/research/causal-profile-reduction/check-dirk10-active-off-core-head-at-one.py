#!/usr/bin/env python3
"""Exact independent replay of the active off-core head-at-one chart."""

from itertools import permutations
import sys

from sympy import GF
from sympy.polys.fields import field


def check(p):
    roots = tuple(v for v in range(p) if (42*v**4-84*v**3+56*v*v-14*v+1) % p == 0)
    fixed = (0, 1, *roots)
    assert len(roots) == 4
    _, t = field("t", GF(p))

    def d(a, b):
        assert b % p
        return a * pow(b % p, -1, p) % p

    def nodal(ns):
        c = [1]
        for z in ns:
            c = [-z*a+b for a, b in zip(c+[0], [0]+c)]
        return c

    def prim(ns, x):
        return sum(coef*x**(i+1)*d(1, i+1) for i, coef in enumerate(nodal(ns)))

    mass = {v: prim([s for s in fixed if s != v], 1) % p for v in roots}
    for x in roots:
        a = d(x*(5-3*x), 5*(2-x))
        radau = 10-12*x+3*x*x
        assert a not in fixed and radau % p
        Sa = d(x**3*(2-x), 12*a*(a-1)*(a-x))
        S1 = d(x**3*(2*a-x), 12*(1-a)*(1-x))
        delta = (d(1-2*a, 12)*S1-(1-d(a, 2))*d(a**3, 6)*Sa) % p
        assert delta and delta == d(x**4*radau**2, 720*(2*x-5)*(x-2)*(x-1))

    orders = 0
    for U, W, R, X in permutations(roots):
        late = d(10*R*U*U-25*R*U*W+10*R*W*W+U*U*W+U*W*W, 6*(U-W)**2)
        assert late not in fixed
        k = {
            U: d(-U**3, 6),
            W: d(W**3*(2*U-W), 6*(U-2*W)),
            R: d(R**3*(2*U-W)*(3*R**2-5*R*(U+W)+10*U*W),
                 6*(4*R*U*U-13*R*U*W+4*R*W*W+U*U*W+U*W*W)),
        }
        E = {s: mass[s]*k[s] % p for s in k}
        assert all(E.values())
        weights = {U: W-R, W: R-U, R: U-W}
        tot = sum(weights[s]*E[s] for s in E)
        a = d(sum(weights[s]*E[s]*s for s in E), tot)
        b = d(-sum(weights[s]*E[s]*s*s for s in E), tot)
        c, d0 = (1-a) % p, (2*a+b-1) % p
        u, v, r, x = [(1-s) % p for s in (U, W, R, X)]
        D, B = t-c, c*t+d0
        T = B-t*D
        assert all(z % p for z in (d0+c*c, c-1, c-r, 2*c+d0-1, 2*c*r+d0-r*r))
        C_t = 42*(t-x)
        C_q = 42*(B-x*D)
        lt = (E[W]*(c-v)-E[U]*(c-u)) % p
        lq = d(E[W]-E[U], c-r)
        l1 = (v-1)*E[U]*(t-u)*(B-u*D)+(1-u)*E[W]*(t-v)*(B-v*D)
        assert lt and lq and l1.numer.degree() == 2
        assert E[W]*(B-v*D)-E[U]*(B-u*D) == lt*(t-r)
        assert E[W]*(t-v)-E[U]*(t-u) == lq*(B-r*D)
        Pt = 10*B-5*(D+B)*t+3*t*t*D
        Pq = 10*t*D**2-5*(1+t)*B*D+3*B**2
        P1 = 10*t*B-5*(t*D+B)+3*D
        A = ((B-D)*t*t*Pt*lt*C_q+(1-t)*D*B*B*Pq*lq*C_t-T*P1*l1*C_t*C_q)/((t-1)*(B-D)*T)
        Bq = D*B*B*(B-2*t*D)*C_t*lq+t*t*(2*B-t*D)*C_q*lt
        B1 = (1-2*t)*C_t*l1+t*t*(2-t)*lt
        Ba = D*B*B*(B-2*D)*lq+(2*B-D)*C_q*l1
        for pol, deg in [(A, 4), (Bq, 6), (B1, 4), (Ba, 4)]:
            assert pol.denom.degree() == 0 and pol.numer.degree() == deg
        assert all(A.numer.gcd(pol.numer).degree() == 0 for pol in (Bq, B1, Ba))
        orders += 1
    assert orders == 24
    print(f"mod {p}: 4 one-late Radau gates and {orders} all-early triples of resultants pass")


if __name__ == "__main__":
    for prime in map(int, sys.argv[1:]) if len(sys.argv) > 1 else (419, 719):
        check(prime)

#!/usr/bin/env python3
"""Independent exact residue replay of the terminal-unique off-core chart."""

from itertools import permutations
import sys

from sympy import GF
from sympy.polys.fields import field


def check(p):
    roots = tuple(v for v in range(p) if (42*v**4-84*v**3+56*v*v-14*v+1) % p == 0)
    assert len(roots) == 4
    fixed = (0, 1, *roots)
    _, t = field("t", GF(p))

    def d(a, b):
        assert b % p
        return a * pow(b % p, -1, p) % p

    def nodal(ns):
        c = [1]
        for z in ns:
            c = [-z*a + b for a, b in zip(c+[0], [0]+c)]
        return c

    def val(cs, x):
        return sum(a*x**i for i, a in enumerate(cs))

    def ip(cs, x):
        return sum(a*x**(i+1)*d(1, i+1) for i, a in enumerate(cs))

    def prim(ns, x):
        return ip(nodal(ns), x)

    H = [0, 1, -14, 56, -84, 42]
    mass = {v: prim([u for u in fixed if u != v], 1) % p for v in roots}
    for v, x in permutations(roots, 2):
        a = d(x*(5*v-3*x), 5*(2*v-x))
        assert a not in fixed
        radau = 10*v*v-12*v*x+3*x*x
        assert radau % p
        Sa = d(x**3*(2*v-x), 12*a*(a-v)*(a-x))
        Sv = d(x**3*(2*a-x), 12*v*(v-a)*(v-x))
        delta = (d(v**3*(v-2*a), 12)*Sv - (v-d(a, 2))*d(a**3, 6)*Sa) % p
        assert delta and delta == d(x**4*radau**2, 720*(2*x-5*v)*(x-2*v)*(x-v))

    n_pin = n_mob = 0
    for U, W, R, X in permutations(roots):
        Z = d(10*R*U*U-25*R*U*W+10*R*W*W+U*U*W+U*W*W, 6*(U-W)**2)
        assert Z not in fixed
        k = {
            U: d(-U**3, 6),
            W: d(W**3*(2*U-W), 6*(U-2*W)),
            R: d(R**3*(2*U-W)*(3*R**2-5*R*(U+W)+10*U*W),
                 6*(4*R*U*U-13*R*U*W+4*R*W*W+U*U*W+U*W*W)),
        }
        E = {u: d(mass[u]*k[u], u) for u in k}
        assert all(E.values())
        x = (1-X) % p
        for V in (1, X, U, W, R):
            tau = (1-V) % p
            s, z, *other = [u for u in (U, W, R) if u != V]
            alpha = d(E[z]*z-E[s]*s, E[z]-E[s])
            beta = d(E[s]*s*s-E[z]*z*z, E[z]-E[s])
            if other:
                r, = other
                S = d(E[s]*s*s-E[r]*r*r+(E[s]-E[r])*beta,
                      (E[s]*s-E[r]*r)-(E[s]-E[r])*alpha)
                P = (alpha*S+beta) % p
                total, product = (2-S) % p, (1-S+P) % p
                q = total-t
                Q = t*t-total*t+product
                test = prim([0, t, q, tau], t)*val(H, q)-prim([0, t, q, tau], q)*val(H, t)
                assert Q.numer.degree() == 2 and Q.numer.gcd(test.numer).degree() == 0
                n_pin += 1
                continue

            c, d0 = (1-alpha) % p, (2*alpha+beta-1) % p
            r, s = (1-s) % p, (1-z) % p
            D, B = t-c, c*t+d0
            T = B-t*D
            Bt = B-tau*D
            q = B/D
            assert (d0+c*c) % p and (tau-c) % p and (c-r)*(c-s) % p
            assert (c*tau+d0-tau*(tau-c)) % p
            F = [a*42 % p for a in nodal([0, x, r, s])]
            K = (t-r)*(t-s)
            Ct = 42*(t-x)
            Cq = 42*(c-r)*(c-s)*(B-x*D)
            assert val(F, t) == t*K*Ct and val(F, q) == B*K*Cq/D**4
            n = prim([0, t, q, x], x)*D
            v = tau*(tau-t)*(tau*D-B)*(tau-x)
            m = ip(F, x) % p
            assert m
            sstar = m*v-val(F, tau)*n
            kk = sstar/K
            assert kk and kk.denom.degree() == 0 and kk.numer.degree() == 0
            Pt = 10*tau*B-5*(tau*D+B)*t+3*t*t*D
            Pq = 10*tau*t*D**2-5*(tau+t)*B*D+3*B**2
            Pv = 10*t*B-5*(t*D+B)*tau+3*tau*tau*D
            num = -kk*D*Ct*B**2*Pq*(t-tau)+tau**3*Ct*Pv*Cq*T*n+kk*t*t*Pt*Cq*Bt
            A = num/(T*(t-tau)*Bt)
            Bq = D*B**2*(B-2*t*D)*Ct+t*t*(2*B-t*D)*Cq
            Btau = tau**3*(tau-2*t)*Ct*n-kk*t*t*(2*tau-t)
            Bafter = kk*D*B**2*(B-2*tau*D)-tau**3*(2*B-tau*D)*Cq*n
            assert n.denom.degree() == 0 and n.numer.degree() == 2
            for pol, deg in [(A, 4), (Bq, 6), (Btau, 4), (Bafter, 4)]:
                assert pol.denom.degree() == 0 and pol.numer.degree() == deg
            assert all(A.numer.gcd(pol.numer).degree() == 0 for pol in (Bq, Btau, Bafter))
            n_mob += 1
    assert (n_pin, n_mob) == (48, 72)
    print(f"mod {p}: 24 location guards, 12 late Radau gates, {n_pin} pinned and {n_mob} Möbius comparisons pass")


if __name__ == "__main__":
    for prime in map(int, sys.argv[1:]) if len(sys.argv) > 1 else (419, 719):
        check(prime)

#!/usr/bin/env python3
"""Exact fixed probes for a conditional ladder; no uniform-node search."""
from fractions import Fraction as F
from itertools import combinations
from math import prod


def require(p, message):
    if not p:
        raise AssertionError(message)


def multiply(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i+j] += a*b
    return r


def nodal(roots):
    r = [F(1)]
    for x in roots:
        r = multiply(r, [-x, 1])
    return r


def L(M, p, j=0):
    require(len(p)+j <= len(M), "required moment present")
    return sum(c*M[i+j] for i, c in enumerate(p))


def cofactor(M, nodes, x):
    return L(M, nodal(y for y in nodes if y != x))


def seed(M, roots, exact=True):
    n = len(roots)
    P = nodal(roots)
    require(len(set(roots)) == n and L(M, P) == L(M, P, 1) == 0, "paid split rule")
    C = {x: cofactor(M, roots, x) for x in roots}
    h, k = L(M, P, 2), L(M, P, 3)
    weights = {x: C[x] / prod(x-y for y in roots if y != x) for x in roots}
    require(all(weights.values()), "every site active")
    actual = [sum(weights[x]*x**j for x in roots) for j in range(n+3)]
    require(actual[:n+2] == M[:n+2] and M[n+2]-actual[n+2] == h,
            "all paid moments and exact first defect")
    if exact:
        require(h != 0, "genuine exact seed")
    return P, C, h, k


def model_normalized(C, h, u, v):
    ell = v-u
    return h/(C[u]*ell**3), -h/(C[v]*ell**3)


def normalized_rank_free(a, b):
    return [a*(b+1)/(a-b), (a-b)/(a+1), (a+1)/(b+1)]


def chi(a, b):
    return (a+b-1)**3 + 27*a*b


def by_pair(M, roots, u, v, selected=None, exact=True):
    P, C, h, k = seed(M, roots)
    ell = v-u
    a, b = model_normalized(C, h, u, v)
    r_u, r_v = ell**2*a, ell**2*b
    z = normalized_rank_free(a, b) if selected is None else selected
    new = [u+ell*t for t in z]
    S = sum(new)
    tau = S-u-v
    G = nodal(new)
    B = lambda X: (X-u)*(X-v)
    valG = lambda X: (X-tau)*B(X)+r_u*(X-v)+r_v*(X-u)
    exactG = multiply([u*v, -u-v, 1], [-tau, 1])
    exactG[0] += -v*r_u-u*r_v
    exactG[1] += r_u+r_v
    require(exactG == G, "literal physical cubic factorization")
    left = [t for t in roots if t not in {u, v}]
    out = left + new
    Q, CQ, hQ, kQ = seed(M, out, exact=exact)
    require(hQ == k-h*S, "unpaid defect update")
    require(kQ == L(M, P, 4)-tau*k-h*(u*u+u*v+v*v)+h*(r_u+r_v),
            "following moment update")
    require(all(CQ[x] == h/B(x) for x in new), "new cofactor update")
    require(all(CQ[x] == (C[x]*valG(x)+h)/B(x) for x in left), "retained cofactor update")
    for x, y in combinations(new, 2):
        ell1 = y-x
        require(model_normalized(CQ, hQ, x, y) ==
                (hQ/h*B(x)/ell1**3, -hQ/h*B(y)/ell1**3), "fresh-pair ray identity")
    if selected is None:
        require(sum(B(x)+B(y) != 0 for x, y in combinations(new, 2)) >= 2,
                "two eligible fresh pairs")
    require(r_u*(u-v) == -h/C[u] and r_v*(v-u) == -h/C[v],
            "formal infinity leading coefficients")
    return out, hQ, a, b


def elliptic(a, b):
    al, be = b-a-1, a*(2*b+1)
    eta, theta = 4*a*b*(a-b), -4*a*a*b*(b+1)
    A, B, C = al*al-4*be, 2*al*eta-4*theta, eta*eta

    def on(P):
        if P is None:
            return True
        x, y = P
        return y*y == x**3+A*x*x+B*x+C

    def plus(P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        x, y = P
        u, v = Q
        if x == u and y+v == 0:
            return None
        slope = (3*x*x+2*A*x+B)/(2*y) if P == Q else (v-y)/(u-x)
        X = slope*slope-A-x-u
        Y = slope*(x-X)-y
        require(on((X, Y)), "elliptic addition")
        return X, Y

    def times(n, P):
        Q = None
        while n:
            if n & 1:
                Q = plus(Q, P)
            P = plus(P, P)
            n //= 2
        return Q

    D, T = (F(0), -eta), (4*a*b, 4*a*b)
    require(chi(a, b) and on(D) and on(T) and times(3, T) is None,
            "smooth rational 3-torsion model")
    require(all(times(j, D) is not None for j in (6, 9, 12)),
            "distinguished infinity difference nontorsion")

    def split_at(P):
        X, Y = P
        x = (Y-al*X-eta)/(2*X)
        U = X/2-(x*x+al*x+be)
        l = x*x+(a+b-1)*x-a
        y = (U+l)/(2*x*(x-1))
        s = x+a/x+b/(x-1)
        z = 1+s-x-y
        require(len({x,y,z}) == 3 and x*y*z == a, "complete split point")
        return [x, y, z]

    return times, D, split_at


# Prescribed moment functional, not uniform integration. Choose its M5
# so that h1/h0=125/12, giving the next normalized pair (8,-1/2).
M = [F(1), F(1,3), F(1,3), F(1,3), F(-1,3), F(-97,18), F(0), F(0)]
r0 = [F(0), F(1)]
want1 = [F(-3), F(-1,2), F(2,3)]
want2 = [F(2,3), F(-31,17), F(-23,36), F(42)]
# The only choice of M6 making the second defect exactly 1.
M[6] = 1-L(M, nodal(want2), 2)
r1, h1, a, b = by_pair(M, r0, *r0)
require(r1 == want1 and (h1,a,b) == (F(-125,18),F(1),F(2)), "first rank-free probe")
r2, h2, a1, b1 = by_pair(M, r1, *r1[:2])
require(r2 == want2 and (h2,a1,b1) == (F(1),F(8),F(-1,2)), "second rank-free probe")
times, D, split_at = elliptic(a,b)
elliptic(a1,b1)
print("Fixed synthetic moments: exact orders 4, 5, 6 on widths 2, 3, 4 by two rank-free moves.")
print("Both chosen rank-free pairs are smooth with the exact [6], [9], [12] nontorsion test.")

alt, alt_h, _, _ = by_pair(M, r0, *r0, selected=split_at(times(3,D)))
_, altC, _, _ = seed(M, alt)
elliptic(*model_normalized(altC, alt_h, *alt[:2]))
print("Rank-assisted [3]D probe: exact order-five seed and nontorsion fresh pair.")

lifted, _, _, _ = by_pair(M, alt, *alt[:2])
spectator = alt[2]
R = nodal(x for x in lifted if x != spectator)
require(lifted[0] == spectator and spectator**2*cofactor(M,lifted,spectator) == L(M,R,2) != 0,
        "spectator lift retains contributing site")
print("Spectator probe: rank-assisted first move lifts the next rank-free move by one order.")

bad = M.copy()
bad[5] = F(14,9)
alt1, bad_h, a_bad, b_bad = by_pair(bad, r0, *r0, exact=False)
require(alt1 == r1 and bad_h == 0 and (a_bad,b_bad) == (a,b), "fixed-rank shortcut fails")
print("Exactness obstruction: one changed unpaid moment makes the same rank-free rule overpay.")

kap, alp = F(2), F(1)
bet = alp*kap**3
delta = 1/(alp*(1+kap)**3)
require(chi(alp*delta,bet*delta) == 0 and chi(alp,bet) != 0, "singular ray parameter")
print("Rational singular-ray check: alpha=1, beta=8, unique nonzero delta=1/27.")
print("PASS: exact identities and synthetic tests only; no uniform seed or stage claim.")

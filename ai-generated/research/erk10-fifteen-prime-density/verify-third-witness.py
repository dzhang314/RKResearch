#!/usr/bin/env python3
"""Replay the third coefficient field, square-class independence, and coverage."""
import ast
from collections import Counter
from fractions import Fraction as F
from math import factorial, prod
from pathlib import Path
import sys
import sympy as S

here = Path(__file__).resolve().parent
sys.path.insert(0, str(here.parent / "erk10-fifteen-fixedq-29adic"))
import origin_polynomial as origin

x = origin.c
h0, f0, k0, j0, a1 = origin.coefficients()
num, den = S.fraction(a1)
[(P, multiplicity)] = [(S.Poly(g, x), m) for g, m in S.factor_list(num, x)[1]
                        if g.subs(x, 2) % 29 == 0]
assert P.degree() == 10 and multiplicity == 1

source = here.parent / "erk10-fifteen-two-pair-rational-closure" / "univariate.py"
defs = {node.targets[0].id: ast.literal_eval(node.value)
        for node in ast.parse(source.read_text()).body
        if isinstance(node, ast.Assign) and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id in ("NONIC", "GRAM", "MN", "NN")}
N, B, M0, N0 = [S.Poly.from_list(defs[k], x, domain=S.ZZ)
                 for k in ("NONIC", "GRAM", "MN", "NN")]
T = M0**2 - 20*B*N0


def frobenius_type(poly, p):
    g = S.Poly(poly, x, modulus=p)
    assert g.degree() == poly.degree() and g.gcd(g.diff()).degree() == 0
    g = g.monic()
    X = S.Poly(x, x, modulus=p)
    h, degs, lengths = X, [], []
    for j in range(1, g.degree() + 1):
        h = (h**p) % g
        degs.append(g.gcd(h-X).degree())
        k = degs[-1] - sum(i for i in lengths if j % i == 0)
        assert k >= 0 and k % j == 0
        lengths += [j] * (k//j)
    assert sum(lengths) == g.degree()
    return tuple(lengths), degs


def head(p):
    def make(z):
        return S.Poly(z, x, modulus=p)

    mod = make(P).monic()
    one, zero = make(1), make(0)

    def div(a, b):
        s, _, g = b.gcdex(mod)
        assert g == one
        return (a*s) % mod

    def ce(z):
        u, v = S.fraction(z)
        return div(make(u), make(v))

    def mul(*vs):
        acc = [one]
        for v in vs:
            r = [zero] * (len(acc)+len(v)-1)
            for i, a in enumerate(acc):
                for j, b in enumerate(v):
                    r[i+j] = (r[i+j]+a*b) % mod
            acc = r
        return acc

    def I(v, shift=0):
        return sum((a*pow(j+shift+1,-1,p) for j,a in enumerate(v)), zero) % mod

    def cst(z):
        return make(z) % mod

    def lin(z):
        return [-z, one]

    c, g, R, d = map(cst, (x,6,15,26))
    h,f,k,j = map(ce, (h0,f0,k0,j0))
    om = (210*c**3-336*c*c+168*c-28) % mod
    e = div(c*(c-d),c+c*om*d)
    Qc,Ql = (e*d*k) % mod, (e*d*(j-div(2*k,c))) % mod
    T3 = mul(lin(f),lin(g),lin(h))
    B0 = mul(lin(zero),lin(one),lin(c),lin(d),lin(e),T3)
    E0,E1 = I(B0),I(B0,1)
    V = [75*c**3-108*c*c+45*c-5,
         -3*(175*c**3-244*c*c+97*c-10),
         3*(350*c**3-476*c*c+183*c-18),
         -15*(42*c**3-56*c*c+21*c-2)]
    beta = div(V[0],T3[0])
    Phi = mul(lin(one),lin(c),lin(d),lin(e),
              [a-beta*b for a,b in zip(V,T3)])
    u=E0*R*c*c-2*Qc*c
    v=-E0*R*c-E0*c*c+E1*c+2*Qc-Ql*c
    w=-E1*R*c*c+Qc*c*c
    uu,vv,ww=-I(Phi,1),I(Phi),I(Phi,2)
    delta=u*vv-v*uu
    s,q=div(v*ww-w*vv,delta),div(w*uu-u*ww,delta)
    return mod, s, q, (s*s-4*q) % mod


def norm(g, v, p):
    n = g.degree()
    first = int(g.resultant(v)) % p
    X = S.Poly(x, x, modulus=p)
    columns = [((X**i)*v) % g for i in range(n)]
    second = int(S.Matrix(n,n,lambda i,j: columns[j].nth(i)).det()) % p
    assert first == second
    return first


def nonsquare(a,p):
    r = pow(a % p, (p-1)//2, p)
    assert r in (1,p-1)
    return int(r == p-1)


for p, typ, receipt in (
    (41, (10,), [0,0,0,0,0,0,0,0,0,10]),
    (53, (1,2,7), [1,3,1,3,1,3,8,3,1,3]),
    (269, (1,1,1,7), [3,3,3,3,3,3,10,3,3,3]),
):
    assert frobenius_type(P,p) == (typ,receipt)
    print("Decic Frobenius", p, typ, receipt)
mod,s,q,H = head(269)
assert [int(H.nth(i)) % 269 for i in range(10)] == [33,261,19,54,156,96,17,10,249,71]
assert norm(mod,H,269) == 88 and nonsquare(88,269)
_,s,q,H = head(29)
assert tuple(int(z.eval(2)) % 29 for z in (s,q,H)) == (2,17,23)
head(53)

basis = {}
for p, bits, old_norm, new_norm, old_type, new_type in (
    (19, "011010", 2, 11, (1,4,4), (1,1,8)),
    (23, "110001", 10, 13, (4,5), (1,9)),
    (31, "101010", 7, 14, (2,7), (3,3,4)),
    (41, "111111", 17, 29, (1,8), (10,)),
    (43, "010011", 42, 17, (1,1,2,2,3), (4,6)),
    (47, "001100", 37, 13, (1,2,6), (1,1,8)),
):
    nty, _ = frobenius_type(N,p)
    pty, _ = frobenius_type(P,p)
    assert (nty,pty) == (old_type,new_type)
    G, _, _, H = head(p)
    t = norm(S.Poly(N,x,modulus=p).monic(), S.Poly(T,x,modulus=p), p)
    h = norm(G,H,p)
    assert (t,h) == (old_norm,new_norm)
    row = (sum(j-1 for j in nty)%2,nonsquare(t,p),
           sum(j-1 for j in pty)%2,nonsquare(h,p),nonsquare(3,p),nonsquare(7,p))
    assert "".join(map(str,row)) == bits
    print("Quadratic characters", p, bits, (t,h))
    b = int(bits,2)
    while b and b.bit_length() in basis:
        b ^= basis[b.bit_length()]
    assert b
    basis[b.bit_length()] = b
assert len(basis) == 6


def partitions(n,k):
    if n == 0:
        yield ()
    for j in range(1,min(n,k)+1):
        for xs in partitions(n-j,j):
            yield (j,*xs)


def no_place(n, usable):
    w = lambda j: F(int(not usable(j))+int(not usable(2*j)),2)
    counts = [F(1)]
    for m in range(1,n+1):
        counts.append(sum(w(j)*counts[m-j] for j in range(1,m+1))/m)
    parts = sum(prod(w(j) for j in xs) /
                prod(j**m*factorial(m) for j,m in Counter(xs).items())
                for xs in partitions(n,n))
    assert counts[-1] == parts
    return parts


def complement(usable):
    return (no_place(9,usable)*no_place(10,usable)*
            F(sum(m for j,m in ((1,1),(2,5),(4,2)) if not usable(j)),8))


expected = (F(535038692663489723,789019852013568000),
            F(2038195978321,2080899072000),
            F(1070788017536573,1391569403904000),F(1))
densities = tuple(1-complement(lambda j: k%j==0) for k in range(1,5))
assert densities == expected
for n in (9,10):
    assert no_place(n,lambda j:j==1) == sum(F((-1)**j,2**j*factorial(j)) for j in range(n+1))
assert 1-no_place(10,lambda j:j==1) == F(1462089259,3715891200)
for k,f in enumerate(densities,1):
    print(f"Specified extension degree {k}: {f} ({float(100*f):.9f}%)")
survival = [complement(lambda j:j<=k) for k in range(5)]
for k,(a,b) in enumerate(zip(survival,survival[1:]),1):
    print(f"Least residue degree {k}: {a-b} ({float(100*(a-b)):.9f}%)")

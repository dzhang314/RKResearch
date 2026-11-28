#!/usr/bin/env python3
"""Exact rooted replay in the literal cubic field and both fixed degree tests."""
import ast
from functools import cache
import json
from math import prod
from pathlib import Path
import sympy as S

here = Path(__file__).resolve().parent
data = json.loads((here / "literal-p181.json").read_text())
p = data["prime"]
assert p == 181 and S.isprime(p)
m = tuple(data["modulus"])
assert m == (29, 125, 85)
X = S.Symbol("X")
poly = lambda c: S.Poly(c, X, modulus=p)
x = poly(X)
F = poly(X**3 + m[2]*X**2 + m[1]*X + m[0])
assert F.is_irreducible
source = here.parent / "erk10-fifteen-two-pair-rational-closure" / "univariate.py"
defs = {}
for node in ast.parse(source.read_text()).body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1:
        target = node.targets[0]
        if isinstance(target, ast.Name) and target.id in ("NONIC","GRAM","MN","NN"):
            defs[target.id] = ast.literal_eval(node.value)
N,B,M0,N0 = (S.Poly.from_list(defs[k], X, modulus=p) for k in ("NONIC","GRAM","MN","NN"))
T = M0*M0 - 20*B*N0
assert N.degree() == 9 and S.gcd(N,N.diff()).degree() == 0
assert S.gcd(N,B*T).degree() == 0
roots = []
xp = x
for _ in range(3):
    xp = (xp**p) % N
    roots.append(S.gcd(N,xp-x).monic())
assert roots == [poly(1),poly(1),F]
assert pow(3,(p-1)//2,p) == 1 and pow(7,(p-1)//2,p) == p-1
# If y²=7, the norm of 147+42y to the prime field is 21³.
assert (147**2-42**2*7) == 21**3
assert pow(21**3,(p-1)//2,p) == p-1
print("Signed-pair nonic gcd degrees", [q.degree() for q in roots])
print("Stepanov: 3 square, 7 and norm of the coupled radicand nonsquare; minimum degree 4")

zero, one = (0,0,0), (1,0,0)
def add(a,b):
    return tuple((u+v) % p for u,v in zip(a,b))
def mul(a,b):
    c = [0]*5
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            c[i+j] += u*v
    for i in (4,3):
        for j,M in enumerate(m):
            c[i-3+j] -= c[i]*M
    return tuple(t % p for t in c[:3])
def total(vals):
    z = zero
    for v in vals:
        z = add(z,v)
    return z
def mm(vals):
    z = one
    for v in vals:
        z = mul(z,v)
    return z
A = tuple(tuple(tuple(v) for v in row) for row in data["A"])
b = tuple(tuple(v) for v in data["b"])
assert len(A) == len(b) == 15 and all(len(row)==i for i,row in enumerate(A))
assert all(len(v)==3 and all(0<=a<p for a in v) for row in (*A,b) for v in row)
# Each rooted tree is a canonical tuple of its child trees. Generate
# forests by increasing child indices rather than ordering labels.
@cache
def trees(n):
    if n == 1:
        return ((),)
    catalog = [(i,t) for i in range(1,n) for t in trees(i)]
    def forests(rem,start):
        if rem == 0:
            yield ()
        for k in range(start,len(catalog)):
            w,t = catalog[k]
            if w > rem:
                break
            for tail in forests(rem-w,k):
                yield (t,)+tail
    return tuple(forests(n-1,0))
@cache
def size(t):
    return 1+sum(map(size,t))
@cache
def density(t):
    return size(t)*prod(map(density,t))
@cache
def stage(t):
    vec = tuple(incoming(u) for u in t)
    return tuple(mm(q[i] for q in vec) for i in range(15))
@cache
def incoming(t):
    return tuple(total(mul(a,z) for a,z in zip(row,stage(t))) for row in A)
def weighted(t):
    return total(mul(B,z) for B,z in zip(b,stage(t)))
counts = [len(trees(n)) for n in range(1,11)]
assert counts == [1,1,2,4,9,20,48,115,286,719]
for n in range(1,11):
    for t in trees(n):
        assert mul((density(t)%p,0,0),weighted(t)) == one, (n,t)
defect = add(mul((11,0,0),weighted(((),)*10)),(p-1,0,0))
assert defect == tuple(data["defect"]) == (101,136,106)
print("Strict 15-stage literal:", sum(counts), "rooted conditions; eleventh-bush defect", defect)

# The actual output clocks recover a and the tail generator f;
# match the three reflected visible labels against the literal.
reflected = [add(one,tuple(-u for u in row)) for row in incoming(())]
a, f, g = (0,1,0),(82,39,112),(103,175,96)
assert all(v in reflected for v in (a,f,g))
def coefficients(q):
    rr = q % F
    return tuple(int(rr.nth(i)) % p for i in range(3))
assert coefficients(N.diff()) == (4,36,151)
# The second root is g, so the derivative of the monic tail quadratic at f is f-g.
assert add(f,tuple(-u for u in g)) == (160,45,16)
assert coefficients(5*B) != zero
# Check both tail relations in the original a-coordinate.
assert total([mul(coefficients(5*B),mul(f,f)),mul(coefficients(-M0),f),coefficients(N0)]) == zero
assert total([mul(coefficients(5*B),mul(g,g)),mul(coefficients(-M0),g),coefficients(N0)]) == zero
print("Matched actual reflected generators and two simple-root Hensel derivatives")

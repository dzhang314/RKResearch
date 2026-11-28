#!/usr/bin/env python3
"""Independent exact ring identities and portable normalized census audit."""
import argparse
import hashlib
from pathlib import Path
import sympy as S
from flint import nmod_poly

p = argparse.ArgumentParser()
p.add_argument("repo", type=Path)
args = p.parse_args()
root = args.repo.resolve()
generated = root / "ai-generated"
research = generated / "research"
local = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def row(s):
    x, y = s.split(None, 1)
    q = Path(y)
    assert len(x) == 64 and not q.is_absolute() and ".." not in q.parts
    return x, q

n = m = 0
for line in (local / "prior.sha256").read_text().splitlines():
    h, rel = row(line)
    proof = root / rel
    assert digest(proof) == h, proof
    n += 1
    for entry in proof.read_text().splitlines():
        expect, leaf = row(entry)
        if leaf.parts[0] == "ai-generated":
            path = root / leaf
        elif leaf.parts[0] in ("research", "lean"):
            path = generated / leaf
        else:
            path = proof.parent / leaf
        assert digest(path) == expect, path
        m += 1
print("Frozen proof dependencies verified:", n, "manifests;", m, "file entries.")

x, y, u, v, a, b, c = S.symbols("X Y u v z0 z1 z2")
I = lambda f: S.integrate(f, (x,0,y))
zero = lambda f: S.expand(f) == 0
P = x*(x-u)*(x-v)
Au = u**3*(2*v-u)
Av = v**3*(2*u-v)
Bu = u**4*(5*v-3*u)
Bv = v**4*(5*u-3*v)
assert zero(12*I(P).subs(y,u)-Au)
assert zero(12*I(P).subs(y,v)-Av)
assert zero(60*I(x*P).subs(y,u)-Bu)
assert zero(60*I(x*P).subs(y,v)-Bv)
delta = 6*u**3*v**3*(u-v)**3
assert zero(Bv*Au-Bu*Av-delta)
print("Both scaled primitive readouts and exact integral nodal determinant verified.")

h0,h1,h2,ga,gb,gc=S.symbols("h0 h1 h2 G0 G1 G2")
H=lambda z:h0+h1*z+h2*z**2
D=(a-b)*(a-c)*(b-c)
k0=(b-c)*(y-b)*(y-c)
k1=(c-a)*(y-a)*(y-c)
k2=(a-b)*(y-a)*(y-b)
e=D*H(y)-k0*H(a)-k1*H(b)-k2*H(c)
assert zero(e)
assert zero(ga*gb*gc*D*H(y) - (
    ga*gb*gc*e + gb*gc*k0*(ga*H(a)) + ga*gc*k1*(gb*H(b)) + ga*gb*k2*(gc*H(c))
))
D*=ga*gb*gc
# Here weighted P/Q reads are kept as equations, not divided.
k, bu, bv, gu, gv, pu, pv, qu, qv = S.symbols("k b_u b_v G_u G_v P_u P_v Q_u Q_v")
s_u=D*(qu-k*pu)
p_u=gu*pu-bu*Au
q_u=gu*qu-bu*Bu
s_v=D*(qv-k*pv)
p_v=gv*pv-bv*Av
q_v=gv*qv-bv*Bv
r_u=gu*s_u+D*k*p_u-D*q_u
r_v=gv*s_v+D*k*p_v-D*q_v
assert zero(r_u-D*bu*(Bu-k*Au))
assert zero(r_v-D*bv*(Bv-k*Av))
assert zero(bu*Au*r_v-bv*Av*r_u-D*bu*bv*delta)
print("Weighted quadratic interpolation and the complete undivided three-ghost torsion transfer verified.")

x,p,q,l,r,d,g,h = S.symbols("X p q l r d g h")
m0 = l*g+r*h
m1 = l*p*g+r*q*h
F = (p-q)*g*h
el = h*(m1-q*m0)
er = g*(p*m0-m1)
assert zero(el-F*l) and zero(er-F*r)
hs1 = 2*(l*p+r*q+d*x)-x**2
hs2 = 3*(l*p**2+r*q**2+d*x**2)-x**3
assert zero(2*F*hs2-3*F*x*hs1-6*(p*p-x*p)*el-6*(q*q-x*q)*er-F*x**3)
hs1 = 2*(l*p+d*x)-x**2
hs2 = 3*(l*p**2+d*x**2)-x**3
assert zero(2*g*hs2-3*g*x*hs1-6*(p*p-x*p)*l*g-g*x**3)
assert zero(2*(3*d*x**2-x**3)-3*x*(2*d*x-x**2)-x**3)
print("Cleared zero-, one-, and two-ghost forward boundary identities verified.")

counts={(a,b,g) for a in range(7) for b in range(7) for g in range(7)
        if a<=2 and g>=3 and a+b+g==6}
assert counts == {(0,0,6),(0,1,5),(0,2,4),(0,3,3),
                  (1,0,5),(1,1,4),(1,2,3),(2,0,4),(2,1,3)}
for d in (1,2,3):
    assert {g for a,b,g in counts if g<=d+2}==set(range(3,d+3))
print("Complete chronological count and all degree cutoffs verified.")

for directory, filename in [
    ("cubic-compact-projection","gamma5-bezout-103.txt"),
    ("cubic-live-global","pair-bezout-103.txt")
]:
    f=research / ("dirk11-thirteen-invisible-six-"+directory) / filename
    F,G,one,U,V=(nmod_poly(list(map(int,l.split())),103) for l in f.read_text().splitlines())
    assert one == 1 and F*U+G*V==one
    print("Independently checked stored GF(103) Bézout identity:", filename)

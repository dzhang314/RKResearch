#!/usr/bin/env python3
"""Exact modular tests and literal generator recovery for two DIRK exports."""

from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
from runpy import run_path
import json

research = Path(__file__).resolve().parent.parent
w11 = research / "causal-profile-reduction"
w14 = research / "dirk11-width14-real-reflected-shell"
alg = run_path(str(w14 / "replay.py"))
Alg, ev, add, mul, divrem = (alg[x] for x in ("Alg", "ev", "add", "mul", "divrem"))

def decode(data, tower, rational):
    if tower is None:
        return rational(data)
    return ev([tower.cast(decode(c, tower.base, rational)) for c in data], tower.gen)

def tower(moduli, rational):
    R = None
    for i, mod in enumerate(moduli):
        R = Alg(R, [decode(x, R, rational) for x in mod], f"generator {i+1}")
    return R

def coeffs_mod(x, residues, p, rational):
    if not residues:
        q = rational(x)
        return (q.numerator * pow(q.denominator, -1, p)) % p
    return ev([coeffs_mod(c, residues[:-1], p, rational) for c in x], residues[-1]) % p

def rat_pair(x):
    return Q(int(x[0]), int(x[1]))

def f10(k):
    return 125*k**3 - 100*k**2 - 87*k + 1314

def make_suffix(y, w, M, Phi, B, unit):
    ly = -ev(M, y)*ev(B, y)/ev(Phi, y)
    lw = -ev(M, w)*ev(B, w)/ev(Phi, w)
    a1 = (lw-ly)/(w-y)
    num = add(mul(M, B), mul(Phi, [ly-y*a1, a1]))
    s, rem = divrem(num, mul([-y, unit], [-w, unit]))
    assert not rem and len(s) == 4
    return [v/s[-1] for v in s]

print("DIRK10: front residues mod 13", [f10(k)%13 for k in range(13)])
assert all(f10(k)%13 for k in range(13)) and 125%13
M = [Q(17264,75), Q(-5656,15)]
Phi = [1,-14,56,-84,42]
B = mul([1,-1], [119,-516,729,-336])
def mod_suffix(p,k):
    def m(q):
        q=Q(q)
        return q.numerator*pow(q.denominator,-1,p)%p
    def div(a,b):
        return m(a*pow(b,-1,p))
    assert f10(k)%p==0 and (375*k*k-200*k-87)%p
    y=div(12948+3125*k,21210+7665*k)
    w=div(-25*(k*k-2*k-24),3*(434+77*k))
    M0=list(map(m,M))
    ly=div(-ev(M0,y)*ev(B,y),ev(Phi,y))
    lw=div(-ev(M0,w)*ev(B,w),ev(Phi,w))
    a1=div(lw-ly,w-y)
    n=[v%p for v in add(mul(M0,B),mul(Phi,[ly-y*a1,a1]))]
    # Monic division over integers, followed by reduction, equals division in F_p.
    s, rem=divrem(n,mul([-y,1],[-w,1]))
    assert all(m(v)==0 for v in rem) and len(s)==4
    S=[div(m(v),m(s[-1])) for v in s]
    return y,w,S

assert mod_suffix(23,18)==(3,18,[21,6,3,1])
assert all(ev([21,6,3,1],x)%23 for x in range(23))
assert mod_suffix(11,9)==(9,1,[1,1,9,1])
def discr_cubic(c,b,a):
    return a*a*b*b-4*b**3-4*a**3*c-27*c*c+18*a*b*c
assert discr_cubic(1,1,9)%11==2 and 2 not in {x*x%11 for x in range(11)}
print("DIRK10: irreducible suffix mod 23; nonsquare discriminant 2 mod 11")

D=json.loads((w11/"dirk-order10-eleven-real-coefficients.json").read_text())
K=tower([D["mod_k"]],rat_pair)
assert [125*x for x in K.mod]==[1314,-87,-100,125]
k=K.gen
y=(12948+3125*k)/(21210+7665*k)
w=-25*(k*k-2*k-24)/(3*(434+77*k))
S=make_suffix(y,w,M,Phi,B,K.one)
assert S==[decode(c,K,rat_pair) for c in D["mod_r8"]]
R=Alg(K,S,"first suffix root")
S2=[decode(c,R,rat_pair) for c in D["mod_r9"]]
assert add(mul([-R.gen,R.one],S2),[])==[R.cast(c) for c in S]
L=Alg(R,S2,"second suffix root")
A=[[decode(c,L,rat_pair) for c in row] for row in D["matrix_lower_triangular"]]
nodes=[sum(row) for row in A]
assert nodes==[decode(c,L,rat_pair) for c in D["nodes"]]
assert nodes[5]==L.cast(y)
assert 3125*21210-12948*7665==-32965170
assert (12948-21210*nodes[5])/(7665*nodes[5]-3125)==L.cast(k)
assert nodes[7:10]==[L.cast(R.gen),L.gen,-L.cast(S[2])-L.cast(R.gen)-L.gen]
print("DIRK10: literal row sums recover the front generator and all suffix roots")

D=json.loads((w14/"tableau.json").read_text())
def is_square_rat(x):
    return x >= 0 and isqrt(x.numerator)**2==x.numerator and isqrt(x.denominator)**2==x.denominator
assert (15*15-4*15)*Q(1,33)**2==Q(5,33)
assert not is_square_rat(Q(5,33)) and not is_square_rat(Q(5,33)/15)
mods=D["relations"]
assert mods[0]==["-15","0","1"]
roots=(12,40,17)
for i,x in enumerate(roots):
    P=[coeffs_mod(c,roots[:i],43,Q) for c in mods[i]]
    assert ev(P,x)%43==0 and sum(j*c*x**(j-1) for j,c in enumerate(P) if j)%43
T=[coeffs_mod(c,roots,43,Q) for c in mods[3]]
assert T==[28,5,1]
assert (T[1]**2-4*T[0])%43==42 and 42 not in {x*x%43 for x in range(43)}
print("DIRK11: independent grid square classes; last discriminant 42 nonsquare mod 43")

L=tower(mods,Q)
A=[[decode(c,L,Q) for c in row] for row in D["A"]]
b=[decode(c,L,Q) for c in D["b"]]
c=[sum(row) for row in A]
R=L.base.base.base
r,u,v=map(L.cast,(R.gen,L.base.base.gen,L.base.gen))
assert 2*(1-c[11])-1==u and 2*(1-c[10])-1==v
assert (33*u*u-15)/2==r
Y=[1-x for x in c]
assert b[11] and Y[13]==L.zero and Y[12]==L.cast(Q(1,2))
assert sum(b[j]*A[j][11]*Y[j]**2 for j in (11,12,13))==b[11]*(L.gen+Y[11]**3/3)
print("DIRK11: literal row sums and the weighted transpose recover all four generators")

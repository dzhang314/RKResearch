#!/usr/bin/env python3
"""Exact projection, prime-field and real-place receipts at (z,u)=(27,4)."""
from sympy import QQ
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_poly, nmod_poly
from fractions import Fraction
from math import prod as product


K,c=field('c',QQ)
R,e=ring('e',K)
S,x=ring('x',R)
u=K(4); z=K(27); m=[z**j/(j+1) for j in range(8)]
def mp(q,k=0):
    return sum((co*m[j+k] for (j,),co in q.items()),R.zero)
def ff(q):
    from math import lcm
    a=q.to_dict()
    D=lcm(*(int(c.denominator) for c in a.values()))
    return fmpz_poly([int(a.get((j,),0)*D) for j in range(q.degree()+1)])
def divat(q,y):
    return q.exquo(x-y)
def prod(it):
    r=S.one
    for p in it:
        r*=p
    return r

v=2*u-1
ys=[K.one,u,v,c]
hull=prod(x-y for y in ys)
A=[mp(hull,j) for j in range(3)]
if A[0]==0:
   assert A[1] and A[2]
   s=A[2]/A[1]
   p=e
else:
   s=e
   p=(e*A[1]-A[2])/A[0]
M=u*u-4*u+2; T=u**3-7*u*u+10*u-2
g=lambda y:(u-3)*(u-2)**2*(y**3/3-y*y)/2-(u-3)*(u-1)*(2*u-3)*(y*y/2-y)+(u-2)*(u-1)**2*(y-1)
f=lambda y:-K(4)/3+(2/M-2)*(y-1)/3
E=lambda y:(u-3)*(u-1)*(2*u-3)+(u-3)*(u-2)**2/2*f(y)-T*(1-y)/M
r=[-K(1)/2,M/2,M*(4*u**3-24*u*u+39*u-17)/(2*T),-g(c)/E(c)]
Q=x*x-s*x+p
L=[rr*mp(divat(hull,y)*Q) for y,rr in zip(ys,r)]
B=L[0]-2*u*L[1]+v*L[2]
D=L[0]-2*L[1]+L[2]
Ec=(u-1)*c*L[3]-(u-c)*L[0]-(c-1)*u*L[1]
Dc=(u-1)*L[3]-(u-c)*L[0]-(c-1)*L[1]
fourth=D*Ec-B*Dc
assert fourth.degree()==2
lead=fourth.LC
def red(q):
    return q.rem(fourth)
def redS(q):
    return S.from_dict({k:red(co) for k,co in q.items()})
# At a root, D*W(y) is (D*y-B)*L_y at the suffix.
# All computations below only need e modulo the quadratic.
WW=((u-x)*red((D-B)*L[0])+(x-1)*red((D*u-B)*L[1]))/(u-1)
W2=redS(WW**2)
U=S.zero
for y,rr,l in zip(ys,r,L):
    p0=divat(hull,y)
    d=K.one
    for yy in ys:
        if yy != y: d*=y-yy
    U+=red((D*y-B)**2*rr*l)*p0/d
U=redS(U)
# Q has leading coeff 1, no division in x.
def rem(q):
    q=redS(q)
    for j in range(q.degree(),1,-1):
        q=redS(q-q.get((j,),R.zero)*Q*x**(j-2))
    return q
KM=(x-s)*A[0]+A[1]
d=rem(KM*hull)
n=rem(W2-KM*U)
I=red(d.get((0,),R.zero)*n.get((1,),R.zero)-d.get((1,),R.zero)*n.get((0,),R.zero))
a,b,c0=[fourth.get((j,),R.zero) for j in [2,1,0]]
p1,p0=[I.get((j,),R.zero) for j in [1,0]]
Res=a*p0**2-b*p0*p1+c0*p1**2
assert Res
NUM,DEN=ff(Res.numer),ff(Res.denom)
content,factors=NUM.factor()
assert NUM==content*product((g**n for g,n in factors),start=fmpz_poly([1]))
selected=[(g,n) for g,n in factors if int(g[0])%19==0]
assert len(selected)==1
H,k=selected[0]
assert k==1 and H.degree()==9 and int(H[1])%19==16
# SymPy normalizes denominator polynomials to primitive up to a rational scale.
# The evaluations below check the original fractions before any modular reduction.
D=-p0/p1
P0=(D*A[1].LC-A[2].LC)/A[0].LC
disc=D*D-4*P0
def eval_mod(f,r,p):
    def go(g):
        out=0
        for (j,),a in g.items():
            a=Fraction(str(a))
            out+=a.numerator*pow(a.denominator,-1,p)*pow(r,j,p)
        return out%p
    return go(f.numer)*pow(go(f.denom),-1,p)%p

assert [eval_mod(k,0,19) for k in (A[0].LC,a,p1,p0,D,P0,disc)] == [7,4,3,4,5,2,17]
assert int(DEN[0])%19
assert nmod_poly(H.coeffs(),19).derivative()(0)==16
# Prime factor of degree 9 is 3: Rabin's irreducibility test suffices.
h29=nmod_poly(H.coeffs(),29)
t29=nmod_poly([0,1],29)
assert h29.degree()==9
assert pow(t29,29**9,h29)==t29
assert h29.gcd(pow(t29,29**3,h29)-t29).degree()==0
# A simple Q17 place of Q(c) at which the early discriminant is nonsquare.
h17=nmod_poly(H.coeffs(),17)
assert h17(13)==0 and h17.derivative()(13)==2
assert eval_mod(disc,13,17)==5 and pow(5,8,17)==16
# A real place of that very same field, with positive early discriminant.
l=Fraction(2001421,1987785)
r=Fraction(2950320,2930219)
assert l<r
def ev_h(x):
    f=Fraction(0)
    for a in reversed(H.coeffs()):
        f=f*x+int(a)
    return f
assert ev_h(l)*ev_h(r)<0
def bound(k):
    v,w=Fraction(0),Fraction(0)
    for j in range(k.degree(),-1,-1):
        b=[v*l,v*r,w*l,w*r]
        a=Fraction(str(k.get((j,),0)))
        v,w=min(b)+a,max(b)+a
    return v,w
nl,nh=bound(disc.numer)
dl,dh=bound(disc.denom)
assert nl>0 and dl>0 or nh<0 and dh<0
print('z=27, u=4: c has degree 9; splitting the early two clocks adds degree 2.')
print('The selected degree-18 field has both Q19 and real embeddings.')
print('H =', H)

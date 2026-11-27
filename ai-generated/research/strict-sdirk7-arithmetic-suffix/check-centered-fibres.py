#!/usr/bin/env python3
"""Exact projective exclusion of four centered arithmetic-suffix cuts.
Usage: python3 check-centered-fibres.py {start,end,forward,other}.
Requires SymPy and python-flint, no floating point or clock scans.
"""
from sympy import QQ, primerange
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_poly
import sys,time
from math import prod as product

K,u=field('u',QQ)
R,e=ring('e',K)
S,x=ring('x',R)
z=2*u; m=[z**j/(j+1) for j in range(8)]
def mp(q,k=0):
    return sum((co*m[j+k] for (j,),co in q.items()),R.zero)
def ff(q):
    from math import lcm
    a=q.to_dict()
    D=lcm(*(int(c.denominator) for c in a.values()))
    return fmpz_poly([int(a.get((j,),0)*D) for j in range(q.degree()+1)])
def certificate(f):
    content, fs=f.factor()
    assert f==content*product((p**m for p,m in fs),start=fmpz_poly([1]))
    stats=[]
    safe={K.zero,K.one}
    if mode in ("start","end"):
        safe.add(K(1)/2)
    for p,m in fs:
        if p.degree()==1:
            root=K(-p[0])/p[1]
            assert root in safe, (mode, "unexpected rational exceptional value",root)
            stats.append((1,m,str(root)))
            continue
        c=[int(e) for e in p.coeffs()][::-1]
        for ell in primerange(2,32768):
            if c[0]%ell==0:
                continue
            def ev(x):
                y=0
                for a in c:
                    y=(x*y+a)%ell
                return y
            if all(ev(j) for j in range(ell)):
                stats.append((p.degree(),m,ell))
                break
        else:
            raise ValueError((mode,"no modular certificate",p.degree(),p))
    return stats
def show(co, name):
    assert co
    print(name,certificate(ff(co.numer)),"den",certificate(ff(co.denom)),flush=True)
def divat(q,y):
    return q.exquo(x-y)
def prod(it):
    r=S.one
    for p in it:
        r*=p
    return r

t0=time.monotonic()
assert len(sys.argv)==2 and sys.argv[1] in ("start","end","forward","other")
mode=sys.argv[1]
v=2*u-1
show(u*u-4*u+2,'M'); show(u**3-7*u*u+10*u-2,'T')
c={'start':K.zero,'end':z,'forward':3*u-2,'other':2-u}[mode]
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
show(A[0].get((0,),K.zero),'quadrature pivot')
M=u*u-4*u+2; T=u**3-7*u*u+10*u-2
g=lambda y:(u-3)*(u-2)**2*(y**3/3-y*y)/2-(u-3)*(u-1)*(2*u-3)*(y*y/2-y)+(u-2)*(u-1)**2*(y-1)
f=lambda y:-K(4)/3+(2/M-2)*(y-1)/3
E=lambda y:(u-3)*(u-1)*(2*u-3)+(u-3)*(u-2)**2/2*f(y)-T*(1-y)/M
r=[-K(1)/2,M/2,M*(4*u**3-24*u*u+39*u-17)/(2*T),-g(c)/E(c)]
show(E(c),'fourth ratio pivot')
Q=x*x-s*x+p
L=[rr*mp(divat(hull,y)*Q) for y,rr in zip(ys,r)]
B=L[0]-2*u*L[1]+v*L[2]
D=L[0]-2*L[1]+L[2]
Ec=(u-1)*c*L[3]-(u-c)*L[0]-(c-1)*u*L[1]
Dc=(u-1)*L[3]-(u-c)*L[0]-(c-1)*L[1]
fourth=D*Ec-B*Dc
assert fourth.degree()==2
lead=fourth.LC
show(lead,'collinearity leading')
def red(q):
    return q.rem(fourth)
def redS(q):
    return S.from_dict({k:red(co) for k,co in q.items()})
print('quad computed',time.monotonic()-t0,flush=True)
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
print('isotropy remainder computed',time.monotonic()-t0,flush=True)
a,b,c0=[fourth.get((j,),R.zero) for j in [2,1,0]]
p1,p0=[I.get((j,),R.zero) for j in [1,0]]
Res=a*p0**2-b*p0*p1+c0*p1**2
assert Res
show(Res,'projection factors')
print(mode,time.monotonic()-t0,flush=True)

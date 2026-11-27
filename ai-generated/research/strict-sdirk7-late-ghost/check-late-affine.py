#!/usr/bin/env python3
"""Exact affine-helper exclusion with terminal set {0,1,4}."""
from sympy import QQ,primerange
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_poly,nmod_poly
from math import prod,lcm
from fractions import Fraction
K,z=field('z',QQ)
R,x=ring('x',K)
a=z-1; ys=[a,K(4),K(0),K(1)]
H=prod(x-y for y in ys)
I=lambda f,j=0:sum((c*z**(i+j)/(i+j+1) for (i,),c in f.items()),K.zero)
A=[I(H,j) for j in range(3)]
B=[I((x-a)*(6-14*x+4*x*x),j) for j in range(3)]
D=A[1]*B[0]-A[0]*B[1]
s=(A[2]*B[0]-A[0]*B[2])/D
p=(A[2]*B[1]-A[1]*B[2])/D
Q=x*x-s*x+p
hulls=[H.exquo(x-y) for y in ys]
Ks=[I(H0*Q) for H0 in hulls]
W0,W1=3*Ks[2],-2*Ks[3]
W=W0+(W1-W0)*x
UR=R.zero
for i,(y,H0,K0) in enumerate(zip(ys,hulls,Ks)):
    UR+=(W0+(W1-W0)*y)**2*H0/(K0*prod(y-v for j,v in enumerate(ys) if j!=i))
pol=(x-s)*A[0]+A[1]
rr1=(pol*H).rem(Q)
rr2=(W*W-pol*UR).rem(Q)
coef=lambda q,j:q.get((j,),K.zero)
F=coef(rr1,0)*coef(rr2,1)-coef(rr1,1)*coef(rr2,0)
def toint(poly):
    d=poly.to_dict()
    den=lcm(*(int(x.denominator) for x in d.values()))
    return fmpz_poly([int(d.get((j,),0)*den) for j in range(poly.degree()+1)])
for name,q in [('pivot',D),('isotropy',F)]:
    f=toint(q.numer)
    co,fac=f.factor()
    assert f==co*prod((g**m for g,m in fac),start=fmpz_poly([1]))
    print(name,[(g.degree(),m) for g,m in fac],flush=True)
    for g,k in fac:
        if g.degree()==1:
            assert not g[0]
            print('only linear root zero',flush=True)
            continue
        for p in primerange(2,500):
            h=nmod_poly(g.coeffs(),p)
            if h.degree()==g.degree() and not h.roots():
                print('projective rootless',g.degree(),p,flush=True)
                break
        else:
            raise AssertionError(('missing projective rootlessness',g.degree()))

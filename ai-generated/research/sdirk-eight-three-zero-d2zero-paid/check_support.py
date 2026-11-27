#!/usr/bin/env python3
from flint import fmpq_poly,fmpq
from math import gcd
from pair_field import K,a,b,o,as_poly,minp,normnum
import sympy as sy
X=fmpq_poly([0,1]);m=X
P=70*m**4-140*m**3+90*m*m-20*m+1
def norms(f):
    from sympy.polys.rings import ring
    from sympy import QQ
    R,v=ring('D',QQ)
    a=lambda p:sum((QQ(int(c.numerator),int(c.denominator))*v**i for i,c in enumerate(p.coeffs())),start=R.zero)
    p=a(P).resultant(a(f))
    return abs(int(p.numerator))
phase=[
 (1-m,m,1),
 (1-m,1-m,0),
 (fmpq_poly([fmpq(1,2)]),fmpq_poly([fmpq(1,2)]),1),
 (4-5*m,1-m,0),
 (3*m-1,1-m,0),
 (fmpq_poly([fmpq(1,2)]),1-m,0),
 ((4-m)/5,(1+m)/5,1),
 ((1+m)/3,(2-m)/3,1),
]
support=[]
for i,(e,g,lastE) in enumerate(phase,1):
    last,penult=(e,m) if lastE else (m,e)
    z=2*penult-last
    U=last-penult
    # q3=0 in the arithmetic branch with k2≠0.
    q3=4*U**3-12*U*U*g+3*U*g*g+2*g**3
    size=70*z**4-140*z**3+90*z*z-20*z+1
    t=(1-z**3)/3-(m+e)*(1-z*z)/2+m*e*(1-z)-g*(z-m)*(z-e)
    qn=norms(q3);sn=norms(size);tn=norms(t)
    D=gcd(gcd(qn,sn),tn)
    raw=D
    for p in (2,3,5,7):
        while D%p==0:D//=p
    support.append(D)

assert support==[1,1,1,103,1,3517,1,1]
x,y=sy.symbols('x y')
L=x**4-2*x**3+sy.Rational(9,7)*x*x-sy.Rational(2,7)*x+sy.Rational(1,70)
rel=y*y-y+x*x-x+sy.Rational(2,7)
basis=sy.groebner([L,rel],y,x,domain=sy.QQ)
def stripped(z,pr):
    for p in pr:
        while z%p==0:z//=p
    return z
for f in (a,b,minp):
    p0=as_poly(f) if f is not minp else f
    assert all(stripped(int(c.denominator),(2,3,5,7,13))==1 for c in p0.values())
for e,z in ((a,x),(b,y)):
    assert basis.reduce(as_poly(e).as_expr().subs(sy.Symbol('T'),x+2*y)-z)[1]==0
assert basis.reduce(minp.as_expr().subs(sy.Symbol('T'),x+2*y))[1]==0
def gate(d,z):
    return (1-z*z)/2-d*(1-z)-(1-d)*(z-d)
for z,pp in ((b,(103,7793)),(1-a,(17,))):
    f=gate(a,z)
    assert all(stripped(int(c.denominator),(2,3,5,7,13))==1 for c in as_poly(f).values())
    assert stripped(normnum(f),(2,3,5,7,13)+pp)==1
print('one-clock support: 13 (coordinate exception),17,103,7793')
print('two-clock support:',support)

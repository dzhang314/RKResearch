#!/usr/bin/env python3
"""Exact asymmetric rank-three elimination; modular certificates for every nonlinear factor."""
from fractions import Fraction as Q
from math import factorial, gcd, prod
import json
from pathlib import Path
from sympy import QQ, Poly, Rational, factor, primerange, resultant
from sympy.polys.fields import field


# Recompute the actual three-donor rank condition with independently
# varying mini clocks t,s.
F,A,T,S,L=field('a,t,s,L',QQ)
O,I=F.zero,F.one
B=(3-5*A)/(5-10*A)
def rp(nodes):
    P=[I]
    for x in nodes:P=[-x*P[0]]+[u-x*v for u,v in zip(P,P[1:])]+[P[-1]]
    return P
def integ(coeffs,z):
    return sum(c*z**(i+1)/(i+1) for i,c in enumerate(coeffs))
def tap(v,j):
    p=(O,A,B,I,v)
    x=p[j]
    q=p[:j]+p[j+1:]
    return integ(rp(q),v)/prod(x-h for h in q)
def det(m,c,d):
    return m[0]*(c[1]*d[2]-c[2]*d[1]) + m[1]*(c[2]*d[0]-c[0]*d[2])+m[2]*(c[0]*d[1]-c[1]*d[0])
mini=(I,T,S)
M=[-integ(rp((O,A,B,I,v)),v) for v in mini]
C=[tap(v,1) for v in mini]
D=[tap(v,2) for v in mini]
cubic=10*A*A-10*A+3
assert det(M,C,D)==-125*S**3*T**3*(2*A-1)**4*(S-1)**3*(S-T)*(T-1)**3*(
    -5*A*A+2*A*S+2*A*T+3*A-S-T)/(
    144*A*(S-A)*(T-A)*(A-1)*(5*A-3)*(5*A-2)*cubic*
    (10*A*S-5*A-5*S+3)*(10*A*T-5*A-5*T+3))
sigma=(5*A*A-3*A)/(2*A-1)
def cfun(v):return v**3*((6*A-3)*v*v+(-15*A+8)*v+10*A-6)/(v-A)
def dfun(v):return v**3*(3*v*v+(-5*A-5)*v+10*A)/((10*A-5)*v+3-5*A)
for v,c,d in zip(mini,C,D,strict=True):
    assert c==-C[0]*cfun(v) and d==D[0]*dfun(v)
quad=2*L**3-3*(1+T+S)*L**2+5*(T+S+T*S)*L-10*T*S
assert integ(rp((O,I,T,S,L)),L)==-L**3*quad/60

# Reduce the three real tap reads, evaluated at the unordered mini pair,
# in a quadratic coefficient algebra. This keeps the resultant small.
F,a,l=field('a,L',QQ)
O,I=F.zero,F.one
sigma=(5*a*a-3*a)/(2*a-1)
pi=-(2*l**3-3*(1+sigma)*l*l+5*sigma*l)/(5*l-10)
def pmul(x,y):
    u,v=x; m,n=y
    return u*m-pi*v*n,u*n+v*m+sigma*v*n
def pinv(x):
    u,v=x
    d=u*u+sigma*u*v+pi*v*v
    return (u+sigma*v)/d,-v/d
def peval(q):
    z=(O,O)
    for u in q:
        p0,p1=pmul(z,(O,I)); z=(p0+u,p1)
    return z
def rat(n,d):return pmul(peval(n),pinv(peval(d)))
c=rat((6*a-3,-15*a+8,10*a-6,O,O,O),(I,-a))
d=rat((F(3),-5*a-5,10*a,O,O,O),(10*a-5,3-5*a))
H=(0,-1,20,-120,300,-330,132)
hc=[u/(2*l)**j for j,u in enumerate(H)]
h=peval(hc[::-1])
gate=det((-I,I,sum(hc)),(c[0],d[0],h[0]),(c[1],d[1],h[1]))
A,L=a.as_expr(),l.as_expr()
G=gate.numer.as_expr()
gp=Poly(G,A,L,domain=QQ)
assert gp.total_degree()==27
assert not gate.denom.is_zero
def strip(a):
    while (g:=gcd(a,factorial(12)))>1:a//=g
    return abs(a)
def ev(P,x):
    u=0
    for p in P:u=u*x+p
    return u
R=sorted({Q(j,m) for m in range(2,13,2) for ell in range(m-12,1) for j in range(ell,ell+13)
     if j not in (0,m,m//2) and strip(ev(H[::-1],Q(j,m)).numerator)==1})
assert R==[Q(1,12),Q(1,6),Q(1,4),Q(1,3),Q(2,3),Q(3,4),Q(5,6),Q(11,12)]
print("actual rank and quadrature determinants checked")
print("possible r =",", ".join(map(str,R)))
bad={Rational(0),Rational(1,2),Rational(1),Rational(2,5),Rational(3,5)}
certificates={}
prime_list=[int(p) for p in primerange(2,4096)]
def candidates(pol):
    assert not pol.is_zero
    scalar,factors=pol.factor_list()
    assert pol==Poly(scalar,*pol.gens,domain=QQ)*prod(p**e for p,e in factors)
    L=[]
    for P,e in factors:
        if P.degree()==1:
            L.append(-P.nth(0)/P.nth(1))
            continue
        _,Z=P.clear_denoms(convert=True)
        _,Z=Z.primitive()
        co=tuple(map(int,Z.all_coeffs()))
        if co not in certificates:
            for p in prime_list:
                if co[0]%p and all(ev(co,r)%p for r in range(p)):
                    certificates[co]=p
                    break
            else:
                raise AssertionError(("no modular certificate",co))
    return set(L)
for r0 in R:
    r=QQ(r0.numerator,r0.denominator)
    lf=1/(2*r)
    if lf==2:
        assert factor((sigma-2).numer.as_expr())==(A-1)*(5*A-2)
        print("r at mini5",str(r), "L=2 direct collision")
    else:
        q=Poly(G.subs(L,lf),A,domain=QQ)
        roots=candidates(q)
        excess=roots-bad
        if r==QQ(1,12):
            assert excess=={Rational(9,5),Rational(6,13)}
            for aa in excess:assert pi.as_expr().subs({A:aa,L:lf})==0
        else:
            assert not excess
        print("r at mini5",str(r),"a roots",list(map(str,sorted(roots))))
    # If r is at either other mini clock, 2Lr is a root of the
    # quadratic. The resultants use its cleared coefficient polynomial.
    X=2*r*l
    E=(X*X-sigma*X+pi).numer.as_expr()
    P=Poly(E,A,L,domain=QQ)
    assert P.gcd(gp).total_degree()==0
    rr=Poly(resultant(P.as_expr(),G,L),A,domain=QQ)
    roots=candidates(rr)
    excess=roots-bad
    if r==QQ(1,6):
        assert excess=={Rational(1,3),Rational(4,5)}
        for aa in excess:
            p=Poly(E.subs(A,aa),L,domain=QQ)
            q=Poly(G.subs(A,aa),L,domain=QQ)
            assert p.gcd(q)==Poly(L-1,L,domain=QQ)
    else:
        assert not excess
    print("r at mini6/7",str(r),"a roots",list(map(str,sorted(roots))))
print("nonlinear factors proved rootless by finite residue checks:",len(certificates))
assert certificates
Path("nonroot-certificates.json").write_text(json.dumps(
    [dict(coefficients=c,prime=p) for c,p in sorted(certificates.items())],indent=2)+"\n")
print("asymmetric rank-three AP13 chart excluded")

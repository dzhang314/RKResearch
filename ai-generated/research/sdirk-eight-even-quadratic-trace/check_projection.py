#!/usr/bin/env python3
"""Exact projection for the symmetric monic quadratic graph."""
import sympy as S
from math import gcd,prod
q,g=S.symbols('q g')
def strip(x):
    assert x
    for p in (2,3,5,7):
        while x%p==0:x//=p
    return x
I=lambda i:S.Rational(1,i+1) if i%2==0 else 0
m0,m2,m4=[I(j+2)+q*I(j) for j in (0,2,4)]
Irr=lambda j:I(j+4)+2*q*I(j+2)+q*q*I(j)
det=m0*m4-m2*m2
A=3*m2*Irr(2)-m4*Irr(0)
B=2*m0*m2*m2-m4*m0*m0
N=(3*q+1)*(35*q*q+90*q+51)
L=180*(q+1)**2*(7*q+3)
assert S.expand(A-2*(q+1)**2*(7*q+3)/105)==0
assert S.expand(B-N/4725)==0
assert S.expand(B*L-2*A*N)==0
R=(2*g-1)**2+q
D=R+4*g*g;U=2*R-2*g*(4*g-2)
F=(-2*D**3+U*D**2+4*U*U*D-U**3)-2*R*(3*U-2*D)*D
Q=4*U**3-12*U*U*D+3*U*D*D+2*D**3
z=2*g*(D+2*U)-D
pin=m2*z*z-m4*D*D
h=m2*(2*m2+6*q*m2-12*g*(m4+q*m2))**2-m4*(2*m4+6*q*m2)**2
def poly(f):
    V=S.Poly(f,q,domain=S.QQ)
    d,P0=V.clear_denoms(convert=True)
    assert strip(int(d))==1
    return P0
def hom(expr):
    P=S.Poly(expr,g)
    degree=P.degree()
    return sum(a*N**i*L**(degree-i)
               for (i,),a in P.terms())
guard=[q,m2,m4,det,m4+q*m2,L,N,hom(R),hom(D)]
G=prod(poly(Q) for Q in guard)
Gf=S.factor_list(G)[1]
def trim(expr):
    c,factors=S.factor_list(poly(hom(expr)))
    result=S.Poly(c,q)
    for f,e in factors:
        # Primitive integer factors of a guarded integer polynomial remain
        # nonzero under specialization whenever the guarded product is nonzero.
        if not any(f==h or f==-h for h,_ in Gf):
            result*=f**e
    return result
pA,pQ,ppin,ph=map(trim,(F,Q,pin,h))
assert [x.degree() for x in (pA,pQ,ppin,ph)]==[10,21,21,11]
norm=lambda p,r:abs(int(S.resultant(p,r)))
As=strip(norm(pA,ph))
Zs=strip(gcd(*(norm(pQ,V) for V in (ppin,ph,ppin+ph))))
Xs=strip(norm(poly(A),poly(B)))
print('A stripped support',As)
print('Z stripped support',Zs)
print('singular stripped support',Xs)
assert As==11**6*965179*3535032504307*3489226706289835873
assert Zs==11**12*1439*420941*48029*434112360658085729
assert Xs==11
assert (2*g*A-B).subs({q:-S.Rational(1,2),g:S.Rational(1,4)})==S.Rational(1,2700)


from flint import nmod_poly
from prime_certificates import PRIMES,certify
from controls import CONTROLS
assert set(PRIMES)=={11}|{x[0] for x in CONTROLS}
assert all(certify(p) for p in PRIMES)
def modpoly(f,p):
    return nmod_poly([int(c)%p for c in reversed(f.all_coeffs())],p)
data={t[0]:t for t in CONTROLS}
for p in PRIMES:
    for phase,ps in [('A',(pA,ph)),('Z',(pQ,ppin,ph))]:
        Q0=modpoly(ps[0],p)
        for f in ps[1:]:Q0=Q0.gcd(modpoly(f,p))
        if p==11:expected=[4,4,1]
        elif phase==data[p][1]:expected=[(-data[p][2])%p,1]
        else:expected=[1]
        assert Q0==nmod_poly(expected,p),(p,phase,Q0,expected)
    if p==11:
        q0=(-3*pow(7,-1,p))%p
        MM0=(q0+pow(3,-1,p))%p;MM2=(q0*pow(3,-1,p)+pow(5,-1,p))%p;MM4=(q0*pow(5,-1,p)+pow(7,-1,p))%p
        assert q0==9 and MM2==MM4!=0
        gm=MM0*pow(1+q0,-1,p)%p
        assert gm==9
        r=lambda y:(y*y+q0)%p
        R0=r(2*gm-1)
        d=(R0+4*gm*gm)%p;n=(2*R0-2*gm*(4*gm-2))%p
        assert n==d!=0 and R0==1 and r(2*gm*3-1)==2
        assert 3*R0!=r(2*gm*3-1)
        print('p11 exceptional diagonal fits no actual third phase')
        continue
    _,ph0,q0,gg,uu,aa,*_=data[p]
    inv=lambda v:pow(v%p,-1,p)
    mm0=(q0+inv(3))%p;mm2=(q0*inv(3)+inv(5))%p;mm4=(q0*inv(5)+inv(7))%p
    assert all(v%p for v in (mm0*mm4-mm2*mm2,mm2,mm4,q0,mm4+q0*mm2))
    w=mm4*inv(mm2)%p
    assert 180*(q0+1)**2*(7*q0+3)*gg%p==(3*q0+1)*(35*q0*q0+90*q0+51)%p
    r=lambda x:(x*x+q0)%p
    R0=r(2*gg-1)
    d=(R0+4*gg*gg)%p;n=(2*R0-2*gg*(4*gg-2))%p
    assert all(v%p for v in (R0,d,gg,uu,1+2*uu-uu*uu))
    assert d*uu%p==n
    H=(-2+uu+4*uu*uu-uu**3)%p
    t=2*uu*(3*uu-2)*inv(H)%p
    assert t
    q3=(1+4*uu-4*uu*uu+2*uu*t)%p
    z3=(2*gg*(1+2*uu)-1)%p
    y=(2*aa-1)%p
    assert y and y*y%p==w
    k2=(2*w+6*q0)%p;g0=(2+6*q0-12*gg*(w+q0))%p
    assert k2 and (k2*y+g0)%p==0
    if ph0=='A':
        assert (2+6*q0-12*gg*q0)%p!=0
        assert q3 and R0*q3%p==r(z3)
    else:assert q3==0 and y==z3
    print('prime-field control',p,ph0,q0,gg,uu,aa)

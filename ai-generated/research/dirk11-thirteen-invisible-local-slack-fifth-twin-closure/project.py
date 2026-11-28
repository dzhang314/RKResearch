#!/usr/bin/env python3
"""Exact Q projection, then an all-branch 180-dimensional unit certificate."""
import argparse
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import sympy as S

X,z,l,Rm,Sm,c0,c1,c2=S.symbols('X z l Rm Sm c0 c1 c2')
J4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x:(2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)
FCO=3*c0**2*c1*c2+18*c0**2*c1+18*c0**2*c2**2+162*c0**2*c2+324*c0**2 \
    -5*c0*c1**2*c2-36*c0*c1**2-9*c0*c1*c2**2-108*c0*c1*c2+18*c0*c2**3 \
    +2*c1**3*c2+16*c1**3-3*c1**2*c2**2

def coeffs_a(c0,c1,c2):
    return [-c0/24,3*c0/8+c1/12,-13*c0/12-7*c1/12-c2/4,c0+c1+c2+1]
def coeffs_b(c0,c1):
    return [c0*c0/16,-3*c0*c0/8-c0*c1/4,c0*c0/2+5*c0*c1/4+c1*c1/4,
            -c0*c1-6*c0-c1*c1]
def pp(poly): return S.Poly(poly,z,domain=S.QQ)
def rat(a):
    a=S.Rational(a); return Fraction(int(a.p),int(a.q))
def ev(cs,t):
    r=t.r.to(0)
    for a in reversed(cs): r=r*t+a
    return r
def pm(p,r):
    if not isinstance(p,S.Poly): p=pp(p)
    return [r.to(rat(p.nth(i))) for i in range(p.degree()+1)] if not p.is_zero else [r.to(0)]
def prim(poly): return [poly[0].r.to(0)]+[q/(i+1) for i,q in enumerate(poly)]

def exact():
    # Meaningful normalized interpolation shape at *every* live slope.
    # This step uses the adjugate before dividing by an actual old m.
    m=X*X+Rm*X+Sm
    de=S.Rational(1,4)-l
    F=X*(X*X/4+Rm*X/3+Sm/2)
    R=S.cancel((F-l*(X-1)*m)/de)
    assert S.cancel(S.Poly(R,X).LC())==1
    def row(f):
        p=S.Poly(S.rem(f,R,X),X)
        return S.Matrix([p.nth(i) for i in range(3)])
    M=S.Matrix.hstack(*(row(X**j*m) for j in range(3)))
    det=S.factor(M.det(method='domain-ge'))
    adj=S.factor(sum(M.adjugate()*row(X*X*(X*X/20+Rm*X/12+Sm/6))))
    assert S.cancel(det+Sm**2*(2*Rm**2-9*Sm)/(9*(4*l-1)**2))==0
    assert S.cancel(adj-Sm**2*(Rm**2-Rm*Sm-6*Sm)/(90*(4*l-1)**2))==0

    d=S.Rational(1,4)-l; C=(c0+c1)*l-c0/2
    A=(S.Rational(1,3)-l)*d*C+l**3-d*c2*l*l
    B=d*C*(c1*l-c0/2)-6*c0*l**3
    assert S.expand(A-sum(q*l**i for i,q in enumerate(coeffs_a(c0,c1,c2))))==0
    assert S.expand(B-sum(q*l**i for i,q in enumerate(coeffs_b(c0,c1))))==0
    assert S.expand(S.resultant(A,B,l)+c0**4*FCO/49152)==0
    print("exact adjugate forces Rm²=(Rm+6)Sm at every live slope; slope cubics result in their 13-term gate",flush=True)

    Q,rem=S.div(J5(z*X)*J4(z)-J4(z*X)*J5(z),X-1,X)
    H=S.Poly(Q,X,domain=S.QQ[z]); h=H.LC()
    assert rem==0 and S.expand(h-132*z**5*J4(z))==0
    cv2=H.nth(3)+h*X; cv1=H.nth(2)+X*cv2; cv0=H.nth(1)+X*cv1
    F0=S.Poly(sum(a*cv0**i*cv1**j*cv2**k*h**(4-i-j-k)
                 for (i,j,k),a in S.Poly(FCO,c0,c1,c2).terms()),X,domain=S.QQ[z])
    d0,rm=F0.pdiv(H)
    assert F0*h**(F0.degree()-H.degree()+1)==d0*H+rm
    known=3046955213389824*z**41*J4(z)**6
    got=S.gcd_list(rm.all_coeffs(),z)
    assert pp(got).monic()==pp(known).monic()
    Q=S.Poly.from_dict({(i,):S.cancel(rm.nth(i)/known) for i in range(rm.degree()+1)},
                      X,domain=S.QQ[z])
    assert Q*known==rm and Q.degree()==3
    proj=pp(H.resultant(Q))
    fac=proj.factor_list()[1]
    assert sorted((p.degree(),n) for p,n in fac)==[(1,15),(4,7),(60,1)]
    assert next(p for p,n in fac if p.degree()==1).monic()==pp(z)
    assert next(p for p,n in fac if p.degree()==4).monic()==pp(J4(z)).monic()
    F60=next(p for p,n in fac if p.degree()==60)
    assert F60.is_irreducible
    K=F60.monic()
    f,g=H,Q
    for guess in (2,1):
        quo,rem=f.pdiv(g)
        assert f*g.LC()**(f.degree()-g.degree()+1)==quo*g+rem and rem.degree()==guess
        f,g=g,rem
    g0=pp(g.nth(0)).rem(K); g1=pp(g.nth(1)).rem(K)
    assert S.gcd(g1,K).is_one
    print("exact clock resultants: irreducible degree 60 after z,J4; normalized fourth is a unique live linear ratio",flush=True)
    return F60,K,H,Q,g0,g1

def run(research,prime,exact_data):
    assert S.isprime(prime) and prime>11
    path=research/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py'
    assert sha256(path.read_bytes()).hexdigest()==Path(__file__).with_name('ring.sha256').read_text().strip()
    Ring=run_path(str(path))['Ring']
    F60,K,H,Q,g0,g1=exact_data
    Fr=Ring('residue',prime=prime)
    Fr.to(rat(F60.LC())).inv()
    A=Ring('ordinary degree-60 z',Fr,pm(K,Fr)[:-1]); Z=A.gen()
    def pe(f): return ev(pm(f,A),Z)
    V=-pe(g0)/pe(g1)
    hs=[pe(H.nth(i))/pe(H.LC()) for i in range(5)]
    k2=hs[3]+V; k1=hs[2]+V*k2; k0=hs[1]+V*k1
    assert ev(hs,V)==0 and ev([pe(Q.nth(i)) for i in range(4)],V)==0
    a=coeffs_a(k0,k1,k2); b=coeffs_b(k0,k1)
    a[3].inv()
    # Exact formal coefficient combinations of the two slope cubics.
    u=[a[3]*b[i]-b[3]*a[i] for i in range(3)]
    t=[u[2]*a[i]-(a[3]*u[i-1] if i else 0) for i in range(3)]
    w=[u[2]*t[i]-t[2]*u[i] for i in range(2)]
    l=-w[0]/w[1]
    assert ev(a,l)==0 and ev(b,l)==0
    de=A.to(Fraction(1,4))-l
    de.inv()
    sm=de*k0/l; rm=de*((k0+k1)*l-k0/2)/(l*l)
    assert rm*rm==(rm+6)*sm
    m=[sm,rm,A.to(1)]; P=[A.to(0),*m]; P0=[A.to(0),k0,k1,k2,A.to(1)]
    # This monic extension includes all three choices of normalized repeat.
    R=Ring('r any old clock',A,[k0,k1,k2]); r=R.gen()
    def re(f): return ev(list(map(R.to,f)),r)
    W0=(re(prim(P0)[1:])/re(m)).v
    assert ev(W0,A.to(1))==0
    al=R.to(l)
    h=-al*(r-1)**2/re(W0)
    q=(h+R.to(de))/(1+al)
    d=(al*q-R.to(de))*(R.to(V)-1)/h
    kV=R.to(ev(P,V))+q*R.to(ev(P0,V))/(R.to(V)-1)
    gate=R.to(ev(prim(P0),V))-kV*R.to(ev(W0,V))-d*R.to(ev(P0,V))
    gate.inv()
    print(f"F{prime}: all guards and actual fourth primitive gate are units in the full rank-180 old-repeat algebra",flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--prime',type=int,action='append')
    a=p.parse_args()
    data=exact()
    for prime in a.prime or [101]:
        run(a.research,prime,data)

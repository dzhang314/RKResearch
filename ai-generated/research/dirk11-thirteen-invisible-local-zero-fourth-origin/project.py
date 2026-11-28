#!/usr/bin/env python3
"""Exact clock reconstruction and immediate origin gate when G_V is absent."""
import argparse
from pathlib import Path
from runpy import run_path
from fractions import Fraction
from hashlib import sha256
import sympy as S

X,z,c0,c1,c2=S.symbols('X z c0 c1 c2')
J4=lambda a:42*a**4-84*a**3+56*a*a-14*a+1
J5=lambda a:(2*a-1)*(66*a**4-132*a**3+84*a*a-18*a+1)
def rat(v):
    v=S.Rational(v); return Fraction(int(v.p),int(v.q))
def zp(q): return S.Poly(q,z,domain=S.QQ)
def ev(poly,y):
    w=y.r.to(0)
    for c in reversed(poly): w=w*y+c
    return w
def pm(q,A):
    if not isinstance(q,S.Poly): q=zp(q)
    return [A.to(rat(q.nth(i))) for i in range(q.degree()+1)] if not q.is_zero else [A.to(0)]
def prim(p): return [p[0].r.to(0)]+[a/(i+1) for i,a in enumerate(p)]

def exact():
    m=X*X-S.Rational(6,5)*X+S.Rational(3,10)
    F=X*(X*X/4-S.Rational(2,5)*X+S.Rational(3,20))
    assert S.rem(F,m,X)==S.Rational(3,100)-9*X/200
    a=S.Poly(S.rem(X**3+c2*X*X+c1*X+c0,m,X),X)
    assert S.expand(20*a.nth(1)+30*a.nth(0)-(30*c0+20*c1+15*c2+12))==0
    H,r=S.div(J5(z*X)*J4(z)-J4(z*X)*J5(z),X-1,X)
    assert r==0
    H=S.Poly(H,X,domain=S.QQ[z]); h=H.LC()
    assert S.expand(h-132*z**5*J4(z))==0
    d2=H.nth(3)+h*X;d1=H.nth(2)+X*d2;d0=H.nth(1)+X*d1
    G=S.Poly(12*h+15*d2+20*d1+30*d0,X,domain=S.QQ[z])
    D=zp(H.resultant(G))
    fac=D.factor_list()[1]
    assert sorted((q.degree(),e) for q,e in fac)==[(1,23),(4,4),(24,1)]
    assert next(q for q,e in fac if q.degree()==1).monic()==zp(z)
    assert next(q for q,e in fac if q.degree()==4).monic()==zp(J4(z)).monic()
    K=next(q for q,e in fac if q.degree()==24)
    assert K.is_irreducible and K.LC()==36806406303744
    f,g=H,G
    for d in (2,1):
        u,v=f.pdiv(g)
        assert v.degree()==d and f*g.LC()**(f.degree()-g.degree()+1)==u*g+v
        f,g=g,v
    u0,u1=(zp(g.nth(i)).rem(K) for i in (0,1))
    assert S.gcd(u1,K).is_one
    print("absent fourth: exact normalized old cubic pin, irreducible degree24, unique live normalized fifth ratio",flush=True)
    return H,G,K,u0,u1

def run(research,p,data):
    assert S.isprime(p) and p>11
    path=research/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py'
    assert sha256(path.read_bytes()).hexdigest()==Path(__file__).with_name('ring.sha256').read_text().strip()
    Ring=run_path(str(path))['Ring']
    H,G,K,u0,u1=data
    F=Ring('residue',prime=p); F.to(rat(K.LC())).inv()
    A=Ring('literal V',F,pm(K.monic(),F)[:-1]); V=A.gen()
    def pc(q):return ev(pm(q,A),V)
    B=-pc(u0)/pc(u1)
    coeff=[pc(H.nth(i))/pc(H.LC()) for i in range(5)]
    assert ev(coeff,B)==0 and ev([pc(G.nth(i)) for i in range(4)],B)==0
    d2=coeff[3]+B; d1=coeff[2]+B*d2; d0=coeff[1]+B*d1
    assert (30*d0+20*d1+15*d2+12)==0
    o,t=A.to(1),A.to(0)
    de=A.to(Fraction(3,100))/(d0-d2*Fraction(3,10)-Fraction(9,25))
    l=A.to(Fraction(1,4))-de; l0=-de*d0*Fraction(10,3)
    e=l+l0; delta=de/e
    de.inv()
    m=[o*Fraction(3,10),-o*Fraction(6,5),o]; P=[t,*m]; P0=[t,d0,d1,d2,o]
    R=Ring('old',A,[d0,d1,d2]); y=R.gen()
    def oe(c):return ev(list(map(R.to,c)),y)
    W0=(oe(prim(P0)[1:])/oe(m)).v
    assert ev(prim(P),o)==0 and ev(prim(prim(P)),o)==0 and ev(prim(P0),o)==0
    x=1/V; (x-1).inv()
    w=ev(W0,x)
    d=l*x+l0+delta*w
    (d*d+delta*(x-1-d)*w).inv()
    print(f"F{p}: immediate silent origin is impossible by a full rank24 commutator unit",flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--prime',type=int,action='append')
    a=p.parse_args()
    data=exact()
    for prime in a.prime or [101]:
        run(a.research,prime,data)

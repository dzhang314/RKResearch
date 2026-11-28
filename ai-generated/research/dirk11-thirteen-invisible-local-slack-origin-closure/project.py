#!/usr/bin/env python3
"""Middle origin contact: exact degree-24 Hankel field and three literal exclusions."""
import argparse
from fractions import Fraction
from functools import reduce
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import sympy as S

Y,Rm,L=S.symbols('Y Rm L')
D_COEFFS=(
 13230407553403392,267011755555336704,2560033911115636032,
 15515373932540530688,66720583231238100312,216624157376204840904,
 551659717737061423011,1130082635219648865498,1894808980190735734167,
 2632104378390201453108,3054596645927716768773,2977744072787067566106,
 2445851225491970931297,1694257629297174734616,988644299887360554264,
 484381594002972945024,198132144903674914032,67083252071878183680,
 18569579306025512448,4129336791223515648,719109191400926976,
 94380143794255872,8771447820072960,514147280633856,14281868906496)
D=S.Poly.from_list(D_COEFFS,gens=Rm,domain=S.QQ)
def rp(e): return S.Poly(e,Rm,domain=S.QQ)
def rat(q):
    q=S.Rational(q); return Fraction(int(q.p),int(q.q))
def ev(poly,x):
    a=x.r.to(0)
    for c in reversed(poly): a=a*x+c
    return a
def pm(q,A):
    if not isinstance(q,S.Poly): q=rp(q)
    return [A.to(rat(q.nth(i))) for i in range(q.degree()+1)] if not q.is_zero else [A.to(0)]
def prim(f): return [f[0].r.to(0)]+[a/(i+1) for i,a in enumerate(f)]
def mul(f,g):
    k=f[0].r; a=[k.to(0)]*(len(f)+len(g)-1)
    for i,b in enumerate(f):
        for j,c in enumerate(g): a[i+j]+=b*c
    return a

def exact():
    # Universal old profile Sm = Rm²/(Rm+6) is paid before this step.
    m=(Rm+6)*Y**2+Rm*(Rm+6)*Y+Rm**2
    F=Y*((Rm+6)*Y**2/4+Rm*(Rm+6)*Y/3+Rm**2/2)
    R=F-L*(Y-1)*m
    H=S.Poly(Y*(1-Y)*R,Y)
    M=[sum(q/S.Integer(i+k+1) for (i,),q in H.terms()) for k in range(6)]
    T=S.Matrix(4,3,lambda i,j:M[i+j])
    Q=[S.Poly(T[list(inds),:].det(method='domain-ge'),L,Rm,domain=S.QQ)
         .clear_denoms()[1].primitive()[1].as_expr()
         for inds in ((0,1,2),(0,1,3),(0,2,3),(1,2,3))]
    proj=[rp(S.resultant(Q[0],q,L)) for q in Q[1:]]
    assert all(not p.is_zero for p in proj)
    assert reduce(S.gcd,proj).monic()==D.monic() and D.is_irreducible
    a,b=(S.Poly(p,L,domain=S.QQ[Rm]) for p in Q[:2])
    for degree in (2,1):
        u,v=a.pdiv(b)
        assert a*b.LC()**(a.degree()-b.degree()+1)==u*b+v and v.degree()==degree
        a,b=b,v
    ratio0=rp(b.nth(0)).rem(D); ratio1=rp(b.nth(1)).rem(D)
    assert S.gcd(ratio1,D).is_one
    print("exact ordinary Hankel projection: one irreducible degree24, lambda a unique live linear ratio",flush=True)
    return M,Q,ratio0,ratio1

def run(research,prime,data):
    assert S.isprime(prime) and prime>11
    path=research/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py'
    assert sha256(path.read_bytes()).hexdigest()==Path(__file__).with_name('ring.sha256').read_text().strip()
    Ring=run_path(str(path))['Ring']
    M,Q,q0,q1=data
    F=Ring('residue',prime=prime)
    F.to(rat(D.LC())).inv()
    K=Ring('degree24 Rm',F,pm(D.monic(),F)[:-1]); r=K.gen()
    def pe(f): return ev(pm(f,K),r)
    l=-pe(q0)/pe(q1); de=K.to(Fraction(1,4))-l
    def met(f): return sum(pe(q)*l**i for (i,),q in S.Poly(f,L).terms())
    assert all(met(q)==0 for q in Q)
    J=list(map(met,M))
    j0,j1,j2,j3=J[:4]
    pivot=j0*j2-j1*j1
    vs=(j0*j3-j1*j2)/pivot; vp=(j1*j3-j2*j2)/pivot
    assert all(J[i+2]-vs*J[i+1]+vp*J[i]==0 for i in range(4))

    U=Ring('V any later root, B=vs−V',K,[vp,-vs])
    V=U.gen(); B=U.to(vs)-V; l=U.to(l); de=U.to(de); r=U.to(r)
    de.inv(); l.inv(); (1+l).inv(); (V-1).inv()
    s=r*r/(r+6)
    c0=l*s/de; c1=((Fraction(1,2)-l)*s+l*r)/de; c2=((Fraction(1,3)-l)*r+l)/de
    zero,one=U.to(0),U.to(1)
    m=[s,r,one]; P=[zero,*m]; P0=[zero,c0,c1,c2,one]
    IP,IP0,IQ=prim(P),prim(P0),prim(mul([-one,one],P))
    PV=ev(P,V); P0V=ev(P0,V); J0V=ev(IP0,V)
    P0V.inv()
    (ev(IQ,V)*P0V-(V-1)*PV*J0V).inv()
    print(f"F{prime}: unmarked fourth impossible, full rank48 primitive unit",flush=True)

    R=Ring('r any old repeat',U,[c0,c1,c2]); x=R.gen()
    def oe(cs): return ev(list(map(R.to,cs)),x)
    W0=(oe(IP0[1:])/oe(m)).v
    assert ev(W0,one)==0
    a=R.to(l); h=-a*(x-1)**2/oe(W0)
    q=(h+R.to(de))/(1+a)
    d=(a*q-R.to(de))*(R.to(V)-1)/h
    kV=R.to(PV)+q*R.to(P0V)/(R.to(V)-1)
    (R.to(J0V)-kV*R.to(ev(W0,V))-d*R.to(P0V)).inv()
    print(f"F{prime}: any old pre-fifth completion impossible, full rank144 fourth compatibility unit",flush=True)

    # No repeats, B unmarked. The match at V gives a quadratic in q.
    w=ev(W0,V)
    lv=[l*(V-1)**2-de*w,(1+l)*w]
    jv=[(V-1)*ev(IP,V)-de*J0V,(1+l)*J0V]
    kv=[PV,P0V/(V-1)]
    fv=mul(kv,lv); fv[0]-=jv[0]; fv[1]-=jv[1]
    # IQ4(B)=0 is a linear polynomial without assuming its leader live.
    b0,b1=ev(IQ,B),ev(IP0,B)
    (fv[0]*b1**2-fv[1]*b0*b1+fv[2]*b0**2).inv()
    print(f"F{prime}: consecutive unmarked fifth impossible, full rank48 undivided resultant unit",flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--prime',type=int,action='append')
    a=p.parse_args()
    data=exact()
    for prime in a.prime or [101]:
        run(a.research,prime,data)

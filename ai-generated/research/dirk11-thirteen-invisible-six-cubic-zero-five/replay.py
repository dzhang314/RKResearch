#!/usr/bin/env python3
"""Exact diagonal projection and five-initial-ghost unit test."""
from argparse import ArgumentParser
from fractions import Fraction
from math import comb
from pathlib import Path
from runpy import run_path
import sympy as S

a,b,X,Y=S.symbols("a b X Y")
c0,c1,c2,V=S.symbols("c0 c1 c2 V")

def J4(x):return 42*x**4-84*x**3+56*x*x-14*x+1
def J5(x):return (2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)

def datomic():
    """Verify the affine-mark determinant before any specialization."""
    R3=Y**3+c2*Y**2+c1*Y+c0
    d=10*Y**2+(5*V+10*c2)*Y+3*V**2+5*V*c2+10*c1
    def comp(P):
        v=S.Poly(S.rem(P,R3,Y),Y)
        return S.Matrix([v.nth(i)for i in range(3)])
    M=S.Matrix.hstack(*(comp(d*Y**i)for i in range(3)))
    N=(M.adjugate()*S.Matrix([-V,1,0])).applyfunc(S.expand)
    q0,q1,q2=N
    N0=-V**2*(9*V**3+15*V**2*c2+25*V*c1+45*c0)
    N1=V*(24*V**3+45*V**2*c2+80*V*c1+150*c0)
    N2=-5*(2*V**3+5*V**2*c2+10*V*c1+20*c0)
    assert all(S.expand(u-v)==0 for u,v in zip(N,(N0,N1,N2)))
    J=12*V**3+15*V**2*c2+20*V*c1+30*c0
    B=comp(q0*Y/2+q1*Y**2/3+q2*Y**3/4)
    A=comp(Y*(q0+q1*Y+q2*Y**2))
    T=S.Matrix.hstack(N,A,B).det()
    assert S.expand(12*T+V**2*J**2*M.det())==0
    print("Exact affine determinant identity passed",flush=True)

def synth(P,x,r):
    p=S.Poly(P,x);n=p.degree()
    out=[None]*n;out[-1]=p.nth(n)
    for i in range(n-1,0,-1):out[i-1]=p.nth(i)+r*out[i]
    return sum(S.expand(co)*x**i for i,co in enumerate(out))

def projection():
    F=S.Poly(J5(b)*J4(a)-J5(a)*J4(b),b).exquo(S.Poly(b-a,b)).as_expr()
    assert S.degree(F,b)==4
    U=synth(synth(J5(X)*J4(a)-J5(a)*J4(X),X,a),X,b)
    R=S.Poly(-U.subs(X,1-Y),Y)
    C=1-a
    G=sum(S.Rational(60,i+2)*R.nth(i)*C**i for i in range(4))
    G=S.Poly(G,a,b).clear_denoms()[1].primitive()[1].as_expr()
    assert S.degree(G,b)==3
    zz=S.factor_list(S.resultant(F,G,b),a)[1]
    assert sorted((S.degree(f,a),m)for f,m in zz)==[(4,4),(24,1)]
    quartic=next(f for f,m in zz if m==4)
    assert S.Poly(quartic,a,domain=S.QQ).monic()==S.Poly(J4(a),a,domain=S.QQ).monic()
    P=S.Poly(next(f for f,m in zz if m==1),a,domain=S.QQ).monic()
    print("Exact resultants: only J4(a) and degree 24",flush=True)
    return F,G,P

def rational(q):
    n,d=S.Rational(q).as_numer_denom()
    return Fraction(int(n),int(d))
def eval_a(P,v):
    acc=v.r.to(0)
    for c in S.Poly(P,a).all_coeffs():acc=acc*v+rational(c)
    return acc
def linear_cofactor(F,G,det):
    R=F[0].r;z=R.to(0);m,n=len(F)-1,len(G)-1
    M=[i*[z]+F[::-1]+(n-2-i)*[z] for i in range(n-1)]+[i*[z]+G[::-1]+(m-2-i)*[z] for i in range(m-1)]
    return [det([row[:-2]+[row[-j-1]]for row in M])for j in range(2)]
def ev(cs,x):
    a=x.r.to(0)
    for c in reversed(cs):a=a*x+x.r.to(c)
    return a
def refl(q):
    n=len(q)-1
    return [sum((-1)**(n+i)*comb(j,i)*q[j] for j in range(i,n+1))for i in range(n+1)]

def certificate(D,F,G,P):
    Ring,quot,det=D['Ring'],D['quot'],D['det']; prime=101
    Z=Ring("prime",prime=prime)
    K=Ring("fourth regular forward clock",Z,
           [Z.to(rational(P.nth(i)))for i in range(24)])
    aa=K.gen()
    def coeff(f,n):return [eval_a(S.Poly(f,b).nth(i),aa) for i in range(n+1)]
    m,n=linear_cofactor(coeff(F,4),coeff(G,3),det)
    bb=-m/n
    print("Exact linear relation has a unit pair pivot modulo 101",flush=True)
    A,B=1-aa,1-bb
    lam=-J5(aa)/J4(aa)
    P5=[(K.to(c)+lam*d)/132
           for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    U=quot(quot(P5,aa),bb); R3=refl(U)
    W=Ring("old reflected triple",K,R3[:-1]); Y=W.gen()
    C0,C1,C2=R3[:3]
    D1=10*Y**2+Y*W.to(5*A+10*C2)+W.to(3*A**2+5*A*C2+10*C1)
    target=(Y-1)*(Y-W.to(B))*J4(Y)*D1
    x=1-Y
    I=ev([K.to(0),K.to(0),*(r/(i+2) for i,r in enumerate(U))],x)
    delta=det(list(zip(I.v,(x*I).v,target.v)))
    delta.inv()
    print("The exact five-zero-read determinant is a unit modulo 101",flush=True)

def main():
    root=Path(__file__).resolve().parent
    parser=ArgumentParser()
    parser.add_argument("--arithmetic",type=Path,default=root.parent/"dirk11-thirteen-invisible-six-constant-exclusion/replay.py")
    D=run_path(str(parser.parse_args().arithmetic))
    datomic()
    certificate(D,*projection())

if __name__=="__main__":main()

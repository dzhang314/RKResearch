#!/usr/bin/env python3
"""Exact rank-72 closure of both multi-ghost reverse gaps."""
from argparse import ArgumentParser
from pathlib import Path
from runpy import run_path

HERE=Path(__file__).resolve().parent

def ringpoly(R):
    zero=R.to(0)
    def trim(a):
        a=list(a)
        while len(a)>1 and a[-1]==0:a.pop()
        return a
    def add(a,b):
        return trim([(a[j] if j<len(a) else zero)+(b[j] if j<len(b) else zero)
                     for j in range(max(len(a),len(b)))])
    def scale(a,t):return trim([r*t for r in a])
    def mul(a,b):
        p=[zero]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):p[i+j]+=x*y
        return trim(p)
    def prim(a):return [zero,*(r/(i+1)for i,r in enumerate(a))]
    return add,scale,mul,prim

def certificate(B,D,F,G,P):
    Ring,quot,det=D['Ring'],D['quot'],D['det']
    ev,refl=B['ev'],B['refl']
    j4,j5=B['J4'],B['J5']
    Z=Ring("prime",prime=101)
    K=Ring("a degree24",Z,[Z.to(B['rational'](P.nth(i)))for i in range(24)])
    a=K.gen()
    symp,ev_a,bvar=B['S'],B['eval_a'],B['b']
    def coeff(f,n):
        x=symp.Poly(f,bvar)
        return [ev_a(x.nth(i),a) for i in range(n+1)]
    m,n=B['linear_cofactor'](coeff(F,4),coeff(G,3),det)
    b=-m/n
    V=1-a
    zero,one=K.to(0),K.to(1)
    lam=-j5(a)/j4(a)
    T5=[(K.to(c)+lam*d)/132
           for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    U=quot(quot(T5,a),b);R3=refl(U)
    C=Ring("old reflected cubic",K,R3[:-1]);Y=C.gen()
    c0,c1,c2=R3[:3]
    d=10*Y**2+Y*C.to(5*V+10*c2)+C.to(3*V**2+5*V*c2+10*c1)
    m=(Y-C.to(V))/d
    k=Y*m
    P0=[zero,*R3]
    add,scale,mul,prim=ringpoly(K)
    def fit(p):
        q=[zero,*p.v]
        q=add(q,scale(P0,-ev(q,V)/ev(P0,V)))
        return (ev(prim(q),Y)/k).v
    r0,r1=fit(m),fit(Y*m)
    IP5=prim(mul([-V,one],P0))
    H=[K.to(v)for v in (0,1,-14,56,-84,42)]
    ratio=ev(IP5,V)/ev(H,V)
    Q0=((ev(IP5,Y)-C.to(ratio)*ev(H,Y))/k).v
    g=[r1[0],r1[1]-r0[0],r1[2]-r0[1],-r0[2]]
    leading=g[-1].inv()
    L=Ring("first reflected gap clock",K,[v*leading for v in g[:-1]])
    z=L.gen()
    c1=L.to(r1[1])-z*L.to(r0[1])
    c2=L.to(r1[2])-z*L.to(r0[2])
    w=-c1/c2-z
    delta=ev(Q0,w)*ev(R3,z)-ev(Q0,z)*ev(R3,w)
    delta.inv()
    print("Both exact reconstruction pivots and the crossing primitive are units modulo 101 in rank 72.",flush=True)

def main():
    cli=ArgumentParser()
    cli.add_argument("--arithmetic",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-constant-exclusion/replay.py")
    cli.add_argument("--first-packet",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-cubic-zero-five/replay.py")
    ns=cli.parse_args()
    B,D=run_path(str(ns.first_packet)),run_path(str(ns.arithmetic))
    B['datomic']()
    certificate(B,D,*B['projection']())

if __name__=="__main__":main()

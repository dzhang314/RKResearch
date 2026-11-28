#!/usr/bin/env python3
"""Independent exact linear obstruction on all 108 final cubic chronologies."""
from fractions import Fraction as Q
from itertools import permutations, combinations
from pathlib import Path
from math import gcd, lcm
from collections import Counter
from sympy import Matrix
import argparse, importlib.util, json

def import_gate(path):
    spec=importlib.util.spec_from_file_location("cubic_gate", path/"check.py")
    mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def mul(M,v,dot):return [dot(t,v) for t in M]

def certificate(a,X,e,U,u,p,r):
    dot,add,sub,scale,hull,lag,jint,ev= a.dot,a.add,a.sub,a.scale,a.hull,a.lag,a.jint,a.ev
    n=len(X)
    assert n==9 and X[-3:]==[r,p,u]
    w=[a.weights[t] for t in X]
    y=[1-t for t in X]
    W=[[m*v**j for m,v in zip(w,y,strict=True)]for j in range(6)]
    Qe=[0]*4
    for L,v in zip(lag([Q(0),u,p,r]),[0,e[-1],e[-2],e[-3]],strict=True):
        Qe=add(Qe,scale(L,v))
    F=[ev(hull([Q(0),u,p,r]),z) for z in X]
    XF=[m*v for m,v in zip(F,X,strict=True)]
    D=sub(e,[ev(Qe,z)for z in X])
    XU=[m*v for m,v in zip(U,X,strict=True)]
    L=lag(y[:3])
    K=[[0]*n for _ in y]
    K[1][:2]=[w[1]*y[1]/(2*w[0]),y[1]/2]
    for i in range(2,n):
        K[i][:3]=[(w[i]*jint(f,y[i])+U[i]*f[2])/w[j] for j,f in enumerate(L)]
    assert mul(K,W[0],dot)==W[1]
    assert mul(K,W[1],dot)==scale(W[2],Q(1,2))
    assert mul(K,W[2],dot)==add(scale(W[3],Q(1,3)),U)
    nulls={j:[-w[j]*ev(f,y[j])/w[h] for h,f in enumerate(L)]+
              [Q(int(i==j)) for i in range(3,n)] for j in range(3,n-3)}
    taps=[(i,j) for i in range(3,n-3) for j in range(3,i+1)]
    cases=[(f,W[3],scale(W[4],Q(1,4))) for f in (F,XF,D)]
    cases +=[(f,U,[0]*n) for f in (F,XF,D)]
    cases +=[(F,W[4],scale(W[5],Q(1,5))),(F,XU,[0]*n)]
    aug=[]
    for f,g,h in cases:
        row=[f[i]*dot(nulls[j],g) for i,j in taps]+[dot(f,sub(h,mul(K,g,dot)))]
        delta=lcm(*(Q(z).denominator for z in row))
        V=[int(delta*t) for t in row]; common=gcd(*V) or 1
        aug.append([v//common for v in V])
    assert len(aug)==8 and all(len(r)==7 for r in aug)
    for indices in combinations(range(8),7):
        A=[aug[i]for i in indices]
        dd=int(Matrix(A).det())
        if not dd:continue
        prime=next(p for p in (11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97)
                   if dd%p)
        C=[[t%prime for t in row]for row in A]
        assert int(Matrix(C).det())%prime==dd%prime
        return dict(u=u,p=p,r=r,nonports=X[:6],rows=indices,minor=dd,prime=prime,
                    residue_rows=C,det_mod_prime=dd%prime)
    raise AssertionError("no augmented minor")


def replay(dir_):
    a=import_gate(dir_)
    rs=[]
    for line in (dir_/"exact-gates.jsonl").read_text().splitlines():
        rj=json.loads(line)
        if not rj.get("unpaid"):continue
        u,p,r=map(Q,(rj["u"],rj["p"],rj["r"]))
        k=Q(rj["unpaid"][0][0]); assert k==Q(2,3)
        last=tuple(map(Q,rj["last2"]))
        mid=next(z for z in a.x[3:] if z not in {u,p,r,*last})
        F3=a.hull([Q(0),u,p])
        D,_,n,_=a.eta_rows(u,p,a.jint(F3,p)/a.jint(F3,u))
        E=dict(zip(a.x,[a.ev(f,k)/a.ev(D,k) for f in n],strict=True))
        U=dict(zip(a.x,[a.ev(f,k) for f in a.U],strict=True))
        for zz in permutations(last):
            X=a.x[:3]+[mid,*zz,r,p,u]
            rs.append(certificate(a,X,[E[z]for z in X],[U[z]for z in X],u,p,r))
    assert len(rs)==108
    print("All 108 augmented 8×7 systems contain a nonzero 7×7 integer minor.")
    print("Coefficient rank 6 and augmented rank 7 in every literal chronology.")
    print("Chosen residue primes:",dict(sorted(Counter(r["prime"] for r in rs).items())))
    return rs


if __name__=="__main__":
    P=argparse.ArgumentParser()
    P.add_argument("--gate-dir",type=Path,default=Path(__file__).resolve().parent.parent/"dirk10-cubic-decoder-ten-mesh-obstruction")
    P.add_argument("--emit",type=Path)
    X=P.parse_args()
    rs=replay(X.gate_dir)
    if X.emit:X.emit.write_text("\n".join(json.dumps(r,separators=(",",":"),default=str)for r in rs)+"\n")

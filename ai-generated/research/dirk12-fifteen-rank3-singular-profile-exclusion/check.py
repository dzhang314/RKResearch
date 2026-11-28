#!/usr/bin/env python3
"""Dependency-free exact fixed-Lobatto receipts for both singular profiles."""
import argparse
from itertools import combinations, permutations
import json
from math import isqrt
from pathlib import Path

D=(-42,840,-5040,12600,-13860,5544)


def replay(p, full=True):
    assert all(p % d for d in range(2,isqrt(p)+1))

    def evaluate(f,u):
        return sum(a*pow(u,j,p) for j,a in enumerate(f)) % p

    roots=[u for u in range(p) if evaluate(D,u)==0]
    assert len(roots)==5 and D[-1]%p and not ({0,1}&set(roots))
    assert set(roots)=={(1-u)%p for u in roots}

    def trim(f):
        f=[a%p for a in f]
        while f and not f[-1]:
            f.pop()
        return f

    def add(f,g):
        h=[0]*max(len(f),len(g))
        for i,a in enumerate(f):
            h[i]+=a
        for i,a in enumerate(g):
            h[i]+=a
        return trim(h)

    def scale(f,a):
        return trim([a*c for c in f])

    def mul(f,g):
        if not f or not g:
            return []
        r=[0]*(len(f)+len(g)-1)
        for i,c in enumerate(f):
            for j,d in enumerate(g):
                r[i+j]+=c*d
        return trim(r)

    def hull(cs):
        f=[1]
        for c in cs:
            f=mul(f,[-c,1])
        return f

    def prim(f,u):
        return sum(a*pow(i+1,-1,p)*pow(u,i+1,p) for i,a in enumerate(f)) % p

    def gcd(f,g):
        while g:
            r=f[:]
            inv=pow(g[-1],-1,p)
            while r and len(r)>=len(g):
                j=len(r)-len(g)
                r=add(r,[0]*j+scale(g,-r[-1]*inv))
            f,g=g,r
        return scale(f,pow(f[-1],-1,p))

    def affine_det(z,v):
        a,b,c=z
        x,y,z=v
        return ((b-a)*(z-x)-(c-a)*(y-x)) % p

    primitive4=[]
    for u in roots:
        others=[z for z in roots if z!=u]
        h=mul(hull([0,u]),[u*u*pow(5,-1,p),-u,1])
        row=[]
        for zz in combinations(others,3):
            values=[evaluate(h,z) for z in zz]
            primitive=[prim(h,z) for z in zz]
            # det [1, z, JH/H], cross-multiplied without any H division
            a,b,c=zz
            r,s,t=values
            x,y,z=primitive
            value=(x*s*t*(c-b)+y*r*t*(a-c)+z*r*s*(b-a))%p
            assert value
            row.append(value)
        primitive4.append(row)
    print(f"p={p}: D roots {roots}; all 20 grade-four primitive determinants nonzero")
    for u,row in zip(roots,primitive4):
        print(f"  u={u}: {' '.join(map(str,row))}")

    cubic_quartic=[]
    if full:
        for u in roots:
            K=[z for z in roots if z!=u]
            U=hull(K)
            F=[prim([0]+U,z) for z in K]
            assert all(F)
            E=[]
            for z in K:
                ez=mul(hull([0,u]),hull(w for w in K if w!=z))
                E.append(scale(ez,pow(evaluate(ez,z),-1,p)))
            lamb=[prim(ez,u) for ez in E]
            Gamma=[[prim(ez,z) for ez in E] for z in K]
            const=sum(a*b for a,b in zip(lamb,F))%p
            assert const
            q=[hull(w for w in K if w!=z) for z in K]
            H=[]
            for a,b,r in zip(lamb,F,q):
                H=add(H,scale(r,a*b))
            assert len(H)==4 and H[-1]==const
            R=[]
            for z,f,gamma in zip(K,F,Gamma):
                v=[]
                for a,b,r in zip(gamma,F,q):
                    v=add(v,scale(r,a*b))
                R.append(scale(mul([z,-1],v),pow(f,-1,p)))
            G=[]
            for i,j,k in combinations(range(4),3):
                det=add(add(scale(R[i],K[k]-K[j]),scale(R[j],K[i]-K[k])),
                        scale(R[k],K[j]-K[i]))
                assert len(det)==5 and gcd(H,det)==[1]
                G.append(det)
            cubic_quartic.append({"pivot":u,"nodes":K,"primitive":F,"constant":const,"H":H,"G":G})
            print(f"  u={u}: constant {const}; cubic degree 3 vs all 4 quartics degree 4, gcd one")
    return {"prime":p,"roots":roots,"profile4":primitive4,"profile5":cubic_quartic}


if __name__=='__main__':
    a=argparse.ArgumentParser()
    a.add_argument('--expanded',type=Path)
    args=a.parse_args()
    rows=[replay(43,False),replay(181),replay(1013)]
    if args.expanded:
        args.expanded.write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')

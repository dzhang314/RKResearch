#!/usr/bin/env python3
"""Deterministic exact construction of the 14-stage F43 DIRK11 shell."""
from pathlib import Path
import argparse
import json
from itertools import product

p=43
def f(a,b=1):return a*pow(b,-1,p)%p
def dot(v,w):return sum(x*y for x,y in zip(v,w))%p
def ps(x,n):return [pow(x,j,p)for j in range(n)]
def prim(x,n,k=0):return [f(x**(j+k+1),j+k+1)for j in range(n)]
def solve(M,b):
    m,n=len(M),len(M[0]);S=[[(x%p)for x in row]+[v%p]for row,v in zip(M,b)]
    piv=[]
    for j in range(n):
        i=len(piv)
        t=next((t for t in range(i,m)if S[t][j]),None)
        if t is None:continue
        S[i],S[t]=S[t],S[i]
        S[i]=[f(x,S[i][j])for x in S[i]]
        for k in range(m):
            if k!=i and S[k][j]:
                a=S[k][j]
                S[k]=[(x-a*y)%p for x,y in zip(S[k],S[i])]
        piv.append(j)
    assert all(not row[-1]for row in S[len(piv):])
    ret=[0]*n
    for i,j in enumerate(piv):ret[j]=S[i][-1]
    assert all(dot(row,ret)==v%p for row,v in zip(M,b))
    return ret,len(piv)
def wvec(c,cols):return [dot(c,x)for x in zip(*cols)]
def baseF(a,v):
    B=[f(11,120),f(27,40),f(27,40),f(-8,15),f(11,120)]
    A=[[0]*7,[f(a,6),f(a,6),0,0,0,0,0], [f(a,6),f(a,3),f(a,6),0,0,0,0],
       [f(a,4),0,0,f(a,4),0,0,0],[0,f(27*a,22),f(27*a,22),f(-16*a,11),0,0,0]]
    c=[sum(row)%p for row in A]
    W=[a*x%p for x in B]+[0,0]
    A.append(W)
    cols=[ps(0,5),ps(a,5),prim(a,5),prim(a,5,1),ps(v,5)]
    U=[[int(j==0)for j in range(7)],[int(j==5)for j in range(7)],W,
       [x*y%p for x,y in zip(W,c)]+[0,0],[int(j==6)for j in range(7)]]
    lift=lambda F:wvec(solve(list(zip(*cols)),F)[0],U)
    bp=lambda x:lift(prim(x,5))
    ep=lambda x:lift(ps(x,5))
    A.append(bp(v))
    return A,bp,ep

def prefix_trees(A,order):
    r=[];degrees=[];D=[]
    for m in range(1,order+1):
        head=len(r)
        def gen(k,i):
            if k==0:yield ();return
            for j in range(i,head):
                if degrees[j]>k:break
                for u in gen(k-degrees[j],j):yield (j,)+u
        for t in gen(m-1,0):
            v=[1]*len(A)
            for j in t:v=[x*y%p for x,y in zip(v,D[j])]
            r.append((m,v));degrees.append(m)
            D.append([m*dot(a,v)%p for a in A])
    return r

def construct():
    grid=[0]+[f(1+z,2)for z in range(p)if z*(33*z**4-30*z*z+5)%p==0]+[1]
    assert grid==[0,22,2,9,35,42,1]
    ids=[0,1,2,3,4,1,2,3,5,6]
    Y=[grid[i]for i in ids]
    X=[(1-y)%p for y in Y]
    w0,_=solve(list(zip(*[ps(i,7)for i in grid])),prim(1,7))
    assert all(dot(w0,[x**k for x in grid])==f(1,k+1)for k in range(12))
    W=[f(w0[i],ids.count(i))for i in ids]
    assert all(W)
    A,bp,ep=baseF(X[-2],X[-3])
    E=[ep(x)for x in X]
    P=[bp(x)for x in X]
    f5=[]
    for m,v in prefix_trees(A,6):
        r=[(x**(m-1)-dot(e,v))%p for x,e in zip(X,E)]
        if m<6:assert not any(r)
        else:f5.append(r)
    r0,r1=Y[1],Y[2]
    ga=f(r0**3,6);gb=5;gd=7
    g=[0,ga,gb,gd,0,-ga%p,-gb%p,-gd%p,0,0]
    Cb,_=solve(list(zip(*[ps(y,3)for y in Y[:3]])),[f(r1),f(r1**2,2),f(r1**3,3)+gb])
    hb=(dot(Cb,[y**3 for y in Y[:3]])-f(r1**4,4))%p
    kb=dot(Cb,g[:3])
    def affine(a,b):return [(a+f((b-a)*(y-r0),r1-r0))%p for y in Y]
    H=[u*v%p for u,v in zip(g,affine(f(3*r0,2),f(hb,gb)))]
    D=[u*v%p for u,v in zip(g,affine(f(r0,2),f(kb,gb)))]
    assert all(sum(w*z for w,z,x in zip(W,g,X)if x==a)%p==0 for a in X)
    lows=[[1]*10,Y,[y**2%p for y in Y],[y**3%p for y in Y],g]
    out=[Y,[f(y**2,2)for y in Y],[(f(y**3,3)+z)%p for y,z in zip(Y,g)],
         [(f(y**4,4)+z)%p for y,z in zip(Y,H)],D]
    cells=[(i,j)for i in range(10)for j in range(min(i+1,7))]
    M=[];rhs=[]
    for i in range(10):
        for v,r in zip(lows,out):
            M.append([v[l] if k==i else 0 for k,l in cells]);rhs.append(r[i])
    for v in f5:
        m=[x*w%p for x,w in zip(v,W)]
        M.append([m[i]*Y[j]**4%p for i,j in cells]);rhs.append(dot(m,[f(y**5,5)for y in Y]))
        M.append([m[i]*Y[j]*g[j]%p for i,j in cells]);rhs.append(0)
    taps,rank=solve(M,rhs)
    L=[[0]*10 for _ in range(10)]
    for (i,j),v in zip(cells,taps):L[i][j]=v
    T=[[f(W[j]*L[j][i],W[i])for j in reversed(range(10))]for i in reversed(range(10))]
    F=[row+[0]*10 for row in A]
    for k,i in enumerate(reversed(range(10))):
        corr=wvec(T[k],E[::-1])
        F.append([(a-b)%p for a,b in zip(P[i],corr)]+T[k])
    B=[0]*7+W[::-1]
    for i,j in [(7,0),(8,5),(9,6)]:
        assert F[i]==F[j],(i,j)
        for row in F:row[j]=(row[j]+row[i])%p
        B[j]=(B[j]+B[i])%p
    keep=[i for i in range(17)if i not in (7,8,9)]
    A=[[F[i][j]for j in keep]for i in keep];B=[B[i]for i in keep]
    C=[sum(row)%p for row in A]
    assert len(B)==len(A)==14
    assert not any(A[i][j]for i in range(14)for j in range(i+1,14))
    return {"field":43,"order":11,"stages":14,"A":A,"b":B,"c":C,"linear_rank":rank,
            "reflected_chronology":Y,"early_reflected_cubic":[ga,gb,gd]}

if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--write",action="store_true")
    args=cli.parse_args();rec=construct()
    file=Path(__file__).with_name("tableau.json")
    if args.write:file.write_text(json.dumps(rec,indent=2)+chr(10))
    else:assert rec==json.loads(file.read_text())
    print("Exact literal F43 tableau rebuilt, linear rank",rec["linear_rank"])

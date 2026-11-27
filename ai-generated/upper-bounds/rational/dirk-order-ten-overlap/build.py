#!/usr/bin/env python3
"""Rational overlapping forward/reversed DIRK blocks, extended to a custom grid."""
from fractions import Fraction as Q
from math import prod

Z, O=Q(0),Q(1)
def dot(x,y):return sum((a*b for a,b in zip(x,y) if a and b),Z)
def vlin(c,u):return [dot(c,col) for col in zip(*u)]
def basis(j,n):return [O if i==j else Z for i in range(n)]
def powers(x,n):return [x**k for k in range(n)]
def ints(x,n,h=0):return [x**(k+h+1)/(k+h+1) for k in range(n)]
def pad(v,n):return list(v)+[Z]*(n-len(v))
def solve(columns,v):
    a=[list(r)+[t] for r,t in zip(zip(*columns),v)]
    assert len(a)==len(columns)==len(v)
    for k in range(len(v)):
        j=next(j for j in range(k,len(a)) if a[j][k])
        a[k],a[j]=a[j],a[k]
        c=a[k][k]
        a[k][k:]=[r/c for r in a[k][k:]]
        for j in range(len(a)):
            if j==k or not a[j][k]:continue
            c=a[j][k]
            a[j][k:]=[x-c*y for x,y in zip(a[j][k:],a[k][k:])]
    return [r[-1] for r in a]
def append(a,r):
    assert len(r)==len(a)+1
    for x in a:x.append(Z)
    a.append(r)
def forward(a,v):
    # A length-five scaled rational DIRK initialization; the fourth and fifth
    # output vectors are the first two anchored prefix moments.
    end=[Q(11,120),Q(27,40),Q(27,40),Q(-8,15),Q(11,120)]
    top=[[Z],[Q(1,6),Q(1,6)],[Q(1,6),Q(1,3),Q(1,6)],
         [Q(1,4),0,0,Q(1,4)],[0,Q(27,22),Q(27,22),Q(-16,11),0]]
    A=[pad([a*t for t in r],5) for r in top]
    c=[sum(r,Z) for r in A]
    w=[a*t for t in end]
    append(A,w+[Z])
    P=[powers(Z,5),powers(a,5),ints(a,5),ints(a,5,1),powers(v,5)]
    U=[basis(0,7),basis(5,7),pad(w,7),pad([r*x for r,x in zip(w,c)],7),basis(6,7)]
    lift=lambda y:vlin(solve(P,y),U)
    append(A,lift(ints(v,5)))
    assert lift(ints(a,5))==A[5]
    return A,lambda x:lift(ints(x,5)),lambda x:lift(powers(x,5))

def reverse(b,d,c):
    a=O
    modes=[Z,a,b,d,c]
    R=[pad([Z],5),pad([a/2,a/2],5)]
    coeff=solve([powers(x,4) for x in [Z,b,a,d]],ints(d,4))
    h=coeff[2]/coeff[1]
    U3=[basis(i,5) for i in range(3)]
    r=vlin(solve([powers(x,3) for x in [Z,a,b]],
                 [x+h*y for x,y in zip(ints(b,3),ints(a,3))]),U3)
    R.append([x-h*y for x,y in zip(r,R[1])])
    p=[x+h*y for x,y in zip(powers(b,4),powers(a,4))]
    u=[x+h*y for x,y in zip(basis(2,5),basis(1,5))]
    P=[powers(Z,4),p,powers(d,4),powers(c,4)]
    U=[basis(0,5),u,basis(3,5),basis(4,5)]
    lift=lambda x:vlin(solve(P,ints(x,4)),U)
    R.extend([lift(d),lift(c)])
    return modes,R,lift

def construct(grid,specials=None,anchors=None):
    assert grid[0]==0 and grid[-1]==1 and len(set(grid))==len(grid)
    q=len(grid)
    M=solve([powers(x,q) for x in grid],ints(O,q))
    assert all(M)
    assert all(dot(M,[x**k for x in grid])==Q(1,k+1) for k in range(10)), ('not a degree-9 grid',grid)
    b,d,c=(1,2,3) if specials is None else specials
    if anchors is None:anchors=(b,4)
    a0,a1=anchors
    assert len({b,d,c})==3 and len({a0,a1})==2 and not ({a0,a1}&{0,q-1,d,c})
    rg,R,rl=reverse(grid[b],grid[d],grid[c])
    ri=len(rg)
    # Every extra representative has only reverse-initial donors.
    # The final representatives in this reverse listing are the
    # three merged rows in exact physical chronology.
    reps=[i for i in range(1,q-1) if i not in {d,c,a0,a1}]+[a0,a1,q-1]
    ids=[grid.index(x) for x in rg]+reps
    w=[M[i]/ids.count(i) for i in ids]
    n=len(w)
    L=[pad(r,n) for r in R]
    for i,j in enumerate(reps,ri):
        phi=rl(grid[j])
        prior=[sum((w[l]*R[l][k] for l in range(ri) if ids[l]==j),Z) for k in range(ri)]
        L.append(pad([(M[j]*x-y)/w[i] for x,y in zip(phi,prior)],n))
    assert [sum(r,Z) for r in L]==[grid[i] for i in ids]
    Tr=[[w[j]*L[j][i]/w[i] for j in reversed(range(n))] for i in reversed(range(n))]
    ix=ids[::-1]
    xx=[1-grid[j] for j in ix]
    A,bp,ep=forward(1-grid[a1],1-grid[a0])
    nf=len(A)
    D=[ep(t) for t in xx]
    A=[pad(r,nf+n) for r in A]
    for t,row in zip(xx,Tr):
        A.append([a-b for a,b in zip(bp(t),vlin(row,D))]+row)
    w0=[Z]*nf+w[::-1]
    merg={nf:0,nf+1:5,nf+2:6}
    for i,j in merg.items():
        assert A[i]==A[j],(i,j)
        for r in A:r[j]+=r[i]
        w0[j]+=w0[i]
    keep=[i for i in range(nf+n) if i not in merg]
    A=[[A[i][j] for j in keep] for i in keep]
    w0=[w0[i] for i in keep]
    assert len(A)==q+6
    assert not any(A[0]) and all(not r[j] for i,r in enumerate(A) for j in range(i+1,len(A)))
    return A,w0

def rooted_check(A,b,p=10):
    n=len(A);av=[];degree=[];fac=[];counts=[]
    for m in range(1,p+1):
        beg=len(degree)
        def trees(k,i):
            if k==0:yield ();return
            for j in range(i,beg):
                if degree[j]>k:break
                for u in trees(k-degree[j],j):yield (j,)+u
        for root in trees(m-1,0):
            s=[prod(av[j][i] for j in root) for i in range(n)]
            f=m*prod(fac[j] for j in root)
            a=dot(b,s)*f
            if a!=1:raise ValueError(('order failure',m,root,a))
            degree.append(m);fac.append(f)
            if m<p:av.append([dot(r,s) for r in A])
        counts.append(len(degree)-beg)
    return counts

def records():
    small = [Q(c) for c in ("0","1/9","4/13","2/5","3/5","9/13","8/9","1")]
    regular = [Q(i,8) for i in range(9)]
    for grid in (small,regular):
        A,b=construct(grid)
        c=[sum(r,Z) for r in A]
        counts=rooted_check(A,b)
        defect=11*dot(b,[x**10 for x in c])-1
        assert defect
        yield {"order":10, "stages":len(A), "grid":list(map(str,grid)),
               "A":[list(map(str,r)) for r in A], "b":list(map(str,b)),
               "c":list(map(str,c)), "unordered_counts":counts,
               "scaled_order_11_star_defect":str(defect)}

if __name__=="__main__":
    import argparse,json
    from pathlib import Path
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--export",action="store_true",help="write exact literal JSON next to this script")
    args=cli.parse_args()
    for rec in records():
        n=rec["stages"]
        path=Path(__file__).with_name(f"dirk10-{n}.json")
        if args.export:path.write_text(json.dumps(rec,indent=2)+chr(10))
        else:assert rec==json.loads(path.read_text()),path
        print(f"{n} stages: {rec['unordered_counts']} exact matches; "
              f"eleventh-star defect {rec['scaled_order_11_star_defect']}.")

#!/usr/bin/env python3
"""Independent exact arithmetic, not a tree-case proof or Lean dependency."""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, prod


def lagrange(x, a):
    return [prod((a-y)/(z-y) for h,y in enumerate(x) if h!=i) for i,z in enumerate(x)]


def extrap(p):
    z=[Q(1,m) for m in range(1,p+1)]
    w=lagrange(z,Q(0))
    assert w==[Q((-1)**(p-m)*m**(p-1),factorial(m-1)*factorial(p-m)) for m in range(1,p+1)]
    assert all(w)
    for n in range(p):
        assert sum(a*x**n for a,x in zip(w,z))==(n==0)
    assert sum(a*x**p for a,x in zip(w,z))==Q((-1)**(p+1),factorial(p))
    return w


@lru_cache(None)
def order(t):
    return 1+sum(map(order,t))


@lru_cache(None)
def tfac(t):
    return order(t)*prod(map(tfac,t))


@lru_cache(None)
def tall(n):
    return () if n==1 else (tall(n-1),)


def shapes(p):
    a=tuple(() for _ in range(p-1))
    b=tall(p)
    c=(tall(p//2),)+tuple(() for _ in range(p-1-p//2)) if p>=2 else ()
    assert all(order(t)==p for t in (a,b,c))
    return a,b,c


def block_table(blocks):
    A=[];b=[]
    for m,v,g in blocks:
        base=len(A)
        for j in range(m):
            A.append({base+i:v/m for i in range(j+1)})
            b.append(g*v/m)
    return A,b


def nodes(A):
    return [sum(row.values(),Q(0)) for row in A]


def mv(A,v):
    return [sum((x*v[j] for j,x in a.items()),Q(0)) for a in A]


def dot(b,v):
    return sum((x*y for x,y in zip(b,v)),Q(0))


def tree_value(A):
    @lru_cache(None)
    def phi(t):
        if not t:
            return (Q(1),)*len(A)
        return tuple(prod(col) for col in zip(*(mv(A,phi(u)) for u in t)))
    return phi


def volterra(A):
    c=nodes(A)
    ans=[]
    for i,row in enumerate(A):
        T={j:(c[i]-c[j])*x for j,x in row.items()}
        for h,x in row.items():
            for j,y in A[h].items():
                T[j]=T.get(j,Q(0))-x*y
        T={j:x for j,x in T.items() if x}
        assert all(j<=i for j in T)
        assert T.get(i,Q(0))==-row.get(i,Q(0))**2
        ans.append(T)
    return ans


def rank(A):
    B={}
    for rr in A:
        r={j:Q(x) for j,x in rr.items() if x}
        while r:
            j=min(r)
            x=r[j]
            if j not in B:
                B[j]={i:y/x for i,y in r.items()}
                break
            for i,y in B[j].items():
                z=r.get(i,Q(0))-x*y
                if z:
                    r[i]=z
                elif i in r:
                    del r[i]
    return len(B)


def restriction(A, lo, hi):
    return [{j-lo:x for j,x in A[i].items() if lo<=j<hi} for i in range(lo,hi)]


def transpose(A):
    ans=[{} for _ in A]
    for i,row in enumerate(A):
        for j,x in row.items():
            ans[j][i]=x
    return ans


def masked_hankel(b,c,U,p):
    v=[prod(x-u for u in U) for x in c]
    d=len(U)
    w=(p-d+1)//2
    a=[dot(b,[z*x**i for x,z in zip(c,v)]) for i in range(2*w-1)]
    return [[{j:a[i+j] for j in range(r)} for i in range(r)] for r in range(1,w+1)]


def exact_paid_step_silence(b,c,TC,U,p):
    d=len(U)
    n=p-d-3
    powers=[[x**i for x in c] for i in range(n+1)]
    mask=[prod(x-u for u in U) for x in c]
    for j,cj in enumerate(powers):
        z=mv(TC,[x*y for x,y in zip(cj,mask)])
        tilde=mv(TC,cj)
        for i in range(n-j+1):
            ci=powers[i]
            assert dot(b,[x*y for x,y in zip(ci,z)])==0
            assert dot(b,[x*y*v for x,y,v in zip(ci,tilde,mask)])==0


def cloned(A,b,sizes,ds):
    s=len(A)
    labels=[i for i,n in enumerate(sizes) for _ in range(n)]
    first=[sum(sizes[:i]) for i in range(s)]
    extra=[j for j,i in enumerate(labels) if first[i]!=j]
    hat=[];bd=[]
    for j,i in enumerate(labels):
        row={first[l]:x for l,x in A[i].items()}
        if j in ds:
            row[j]=ds[j]
            row[first[i]]=row.get(first[i],Q(0))-ds[j]
        hat.append({l:x for l,x in row.items() if x})
        bd.append(b[i]/sizes[i])
    assert set(extra)==set(ds)
    assert nodes(hat)==[nodes(A)[i] for i in labels]
    for i in range(s):
        assert sum(bd[first[i]:first[i]+sizes[i]],Q(0))==b[i]
    return hat,bd,labels,first,extra


def exact_intertwining(M,M0,labels,first):
    # Independent column aggregation checks M P = P M0 and E M = M0 E.
    for j,row in enumerate(M):
        agg={}
        for k,x in row.items():
            agg[labels[k]]=agg.get(labels[k],Q(0))+x
        assert {k:x for k,x in agg.items() if x}==M0[labels[j]]
    for i,row in enumerate(M0):
        assert M[first[i]]=={first[l]:x for l,x in row.items()}


def clone_order_twenty(prefix):
    p=20
    w=extrap(p)
    seq=[4,*[i for i in range(1,p+1) if i!=4]] if prefix else [*[i for i in range(1,p+1) if i!=4],4]
    A,b=block_table((m,Q(1),w[m-1]) for m in seq)
    s=len(A)
    assert s==210 and all(b) and all(A[i].get(i) for i in range(s))
    c=nodes(A)
    cut=4 if prefix else s-4
    U=sorted(set(c[:cut] if prefix else c[cut:]))
    assert U==[Q(1,4),Q(1,2),Q(3,4),Q(1)]
    oldphi=tree_value(A)
    for t in shapes(p):
        assert tfac(t)*dot(b,oldphi(t))==1
    t=tall(p+1)
    assert dot(b,oldphi(t))==Q(1+(-1)**(p+1),factorial(p+1))!=Q(1,factorial(p+1))
    for j in range(p):
        assert dot(b,[x**j for x in c])==Q(1,j+1)
    H=masked_hankel(b,c,U,p)
    hr=list(map(rank,H))
    assert sum(hr)>=28
    T=volterra(A)
    sizes=[1]*s
    counted=4 if prefix else 0
    sizes[counted]=4
    first=sum(sizes[:counted])
    pos=range(first+1,first+4)
    vals=[(Q(1,7),Q(1,9),Q(1,11)),(Q(1,7),Q(0),Q(1,11)),(Q(0),)*3]
    out=[]
    hats=[]
    for v in vals:
        ds=dict(zip(pos,v))
        Ad,bd,labels,reps,extra=cloned(A,b,sizes,ds)
        cd=nodes(Ad)
        cutd=sum(sizes[:cut])
        assert len(Ad)==213 and all(bd)
        assert sorted(set(cd[:cutd] if prefix else cd[cutd:]))==U
        exact_intertwining(Ad,A,labels,reps)
        Td=volterra(Ad)
        exact_intertwining(Td,T,labels,reps)
        for j in extra:
            assert [row.get(j,Q(0)) for row in Td]==[-ds[j]**2 if i==j else 0 for i in range(len(Td))]
        pair=restriction(Td,cutd,len(Td)) if prefix else transpose(restriction(Td,0,cutd))
        cor=len(pair)-rank(pair)
        assert cor==sum(x==0 for x in v)
        assert masked_hankel(bd,cd,U,p)==H
        # Rank sees the genuine unchanged cover; particular tree tests see
        # exact values, and the intertwining proves this for all trees.
        ph=tree_value(Ad)
        for t in (*shapes(p),tall(p+1)):
            assert ph(t)==tuple(oldphi(t)[i] for i in labels)
            assert dot(bd,ph(t))==dot(b,oldphi(t))
        out.append(cor)
        hats.append((Ad,bd,cd,Td))
    assert all(b1==hats[0][1] and c1==hats[0][2] for _,b1,c1,_ in hats)
    _,bd,cd,Td=hats[0]
    exact_paid_step_silence(bd,cd,Td,U,p)
    return out,hr


def distinct_blocks(p,prefix):
    ww=extrap(p)
    B=p*(p+2)
    blocks=[]
    for m,w in enumerate(ww,1):
        a=[1+Q((m-1)*(p+2)+i+1,2*p*p*(B+1)) for i in range(p+2)]
        v=lagrange(a,Q(1))
        assert all(v) and all(1<x<1+Q(1,2*p*p) for x in a)
        for d in range(p+2):
            assert sum(b*x**d for b,x in zip(v,a))==1
        blocks.extend((m,x,w*b) for x,b in zip(a,v))
    i=next(i for i,(m,x,g) in enumerate(blocks) if m==4)
    d=blocks.pop(i)
    return [d,*blocks] if prefix else [*blocks,d]


def stage_packet_values(p,pivot,theta,w,delta):
    @lru_cache(None)
    def f(t,x):
        return prod((x-delta)*pivot**(order(u)-1)+delta*f(u,x) for u in t)
    for t in (*shapes(p),()):
        assert sum(a*f(t,x) for x,a in zip(theta,w))==0
    return f


def extend(A,b,k,pivot,theta,w,delta):
    m=len(theta)
    def idx(i):
        return i if i<k else i+m
    ans=[{idx(j):a for j,a in A[i].items()} for i in range(k)]
    for j,c in enumerate(theta,k):
        ans.append({i:x for i,x in ((pivot,c-delta),(j,delta)) if x})
    ans.extend({idx(j):a for j,a in A[i].items()} for i in range(k,len(A)))
    return ans,b[:k]+w+b[k:]


def distinct_case(p,prefix,actual_dense):
    blocks=distinct_blocks(p,prefix)
    c=[x*j/m for m,x,g in blocks for j in range(1,m+1)]
    b=[g*x/m for m,x,g in blocks for j in range(m)]
    assert len(c)==p*(p+1)*(p+2)//2 and len(set(c))==len(c) and all(b)
    assert all(0<x<2 for x in c)
    cut=4 if prefix else len(c)-4
    u=c[:cut] if prefix else c[cut:]
    assert len(set(u))==4
    insertion=len(c) if prefix else cut
    theta=[Q(j+2) for j in range(p+1)]
    w=[1/prod(x-y for y in theta if y!=x) for x in theta]
    assert all(w) and set(theta).isdisjoint(c)
    for j in range(p):
        assert sum(a*x**j for x,a in zip(theta,w))==0
    pivot=c[0]
    fns=[stage_packet_values(p,pivot,theta,w,d) for d in (Q(0),Q(1))]
    # Pure moments stay identical even if these typed-order tests do not.
    if actual_dense:
        A,b0=block_table(blocks)
        assert nodes(A)==c and b0==b
        ph=tree_value(A)
        for t in shapes(p):
            assert tfac(t)*dot(b,ph(t))==1
        size=[]
        for d,fn in zip((Q(0),Q(1)),fns):
            Ad,bd=extend(A,b,insertion,0,theta,w,d)
            assert nodes(Ad)==c[:insertion]+theta+c[insertion:] and all(bd)
            newcut=cut if prefix else cut+p+1
            assert (nodes(Ad)[:newcut] if prefix else nodes(Ad)[newcut:])==u
            Td=volterra(Ad)
            pair=restriction(Td,newcut,len(Td)) if prefix else transpose(restriction(Td,0,newcut))
            cor=len(pair)-rank(pair)
            assert cor==(p+1 if not d else 0)
            do=tree_value(Ad)
            for t in shapes(p):
                assert do(t)[insertion:insertion+p+1]==tuple(fn(t,x) for x in theta)
                assert tfac(t)*dot(bd,do(t))==1
            size.append(cor)
        return len(c),size
    return len(c),None


if __name__=='__main__':
    for p in range(1,21):
        extrap(p)
    print('Exact rational Euler extrapolation moments checked for p=1,...,20.')
    for left in (True,False):
        name='counted suffix column' if left else 'counted prefix dual'
        out,hr=clone_order_twenty(left)
        print(f'Order 20, 213 stages, exactly four discarded clocks, {name}: kernel {out} as clone pivots change; fixed paid Hankel ranks {hr}, all paid inserted-step tests zero.')
    for p in (5,20):
        for left in (True,False):
            n,z=distinct_case(p,left,p==5)
            orientation='suffix column' if left else 'prefix dual'
            print(f'Distinct clocks, p={p}, {orientation}: {n} base stages plus {p+1} live packet stages; exact interpolation/packet tests' +
                  (f', actual local nullities {z}.' if z is not None else '.'))

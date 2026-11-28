"""Exact old-bank construction and elementary arithmetic (standard library)."""
from fractions import Fraction as Q
from functools import cache
from math import prod

def pmul(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]+=x*y
    return tuple(c)

def ev(a,x):
    r=0
    for z in reversed(a):
        r=r*x+z
    return r

def prim(a):
    return (Q(0),)+tuple(x/(i+1) for i,x in enumerate(a))

@cache
def cardinals(xs):
    return tuple(tuple(
        a/prod(x-y for y in xs if x!=y)
        for a in prodpoly(tuple((-y,Q(1)) for y in xs if x!=y)))
        for x in xs
    )

def prodpoly(ls):
    acc=(Q(1),)
    for p in ls:
        acc=pmul(acc,p)
    return acc

def taps(xs,c):
    return [ev(prim(f),c) for f in cardinals(tuple(xs))]

def vecmul(a,b):
    return [x*y for x,y in zip(a,b,strict=True)]

def lin(A,v):
    return [sum(x*y for x,y in zip(row,v,strict=True) if x) for row in A]

def span_basis(rows):
    leads={}
    keep=[]
    for r0 in rows:
        v=list(r0)
        for j in sorted(leads):
            if v[j]:
                t=v[j]
                v=[a-t*b for a,b in zip(v,leads[j],strict=True)]
        k=next((i for i,x in enumerate(v) if x),None)
        if k is not None:
            leads[k]=[x/v[k] for x in v]
            keep.append(r0)
    return keep

def old_bank(last=Q(1,11), s8=Q(4,7), fa=Q(1,4), fb=Q(1,2), fc=Q(3,4), ab=Q(1,3)):
    # prepare real size-six port using the scalar degree-four extra moment.
    bb=(3-5*ab)/(5-10*ab)
    s5,s6,s7=fa*s8,fb*s8,fc*s8
    assert len({fa,fb,fc,1})==4
    assert ev(prim(prodpoly(tuple((-z,Q(1)) for z in (0,fa,fb,fc,1)))),Q(1))==0
    c=[Q(0),ab*s5/4,ab*s5/2,ab*s5,bb*s5,s5,s6,s7,s8,last]
    pids=(0,5,6,7,8,9)
    assert len(set(c))==len(c)
    donor=((),(0,1),(0,1,2),(0,2,3),(0,2,3,4),(0,3,4,5),
           (0,3,4,5,6),(0,3,4,5,7),(0,5,6,7,8),pids)
    A=[[Q(0)]*10 for _ in c]
    for i in range(1,10):
        for j,u in zip(donor[i],taps([c[j] for j in donor[i]],c[i]),strict=True):
            A[i][j]=u
    assert lin(A,[Q(1)]*10)==c
    cells=[]
    for sz in range(1,8):
        layer=[]
        def grow(rem,k,fac,v):
            if rem==0:
                for i in pids if sz<=6 else pids[-2:]:
                    assert v[i]==c[i]**(sz-1)*Q(sz,fac),(sz,i)
                layer.append((sz,fac,v,lin(A,v)))
            for i in range(k,len(cells)):
                t,g,w,Aw=cells[i]
                if t>rem:
                    break
                grow(rem-t,i,fac*g,vecmul(v,Aw))
        grow(sz-1,0,sz,[Q(1)]*10)
        assert len(layer)==(1,1,2,4,9,20,48)[sz-1]
        cells.extend(layer)
    pol=cardinals(tuple(c[j] for j in pids))
    resid=[]
    for sz,fac,v,_ in cells:
        if sz != 7:
            continue
        out=[-sum(v[j]*P0[k] for j,P0 in zip(pids,pol,strict=True)) for k in range(6)]
        assert out[0]==0
        out.append(Q(sz,fac))
        resid.append(out)
    F6=span_basis(resid)
    assert len(F6)<=4
    return A,c,pids,F6

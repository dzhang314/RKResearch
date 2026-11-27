#!/usr/bin/env python3
"""An exact bounded-d rational search on two single-pair clean charts.

At each d the test checks every rational z, without bounding z.
Only a literal all-tree exact verification is considered a witness.
"""
from functools import lru_cache
from fractions import Fraction as Q
from math import gcd, prod
from flint import fmpz_poly,nmod_poly
import sympy as S
import argparse
from clean_chronology import chronology, x,y,u,z,d,h,k,I

def rational(F):
    return Q(int(F.p),int(F.q))

def linear(rows,rhs,n):
    A=[list(map(Q,r))+[Q(v)] for r,v in zip(rows,rhs)]
    piv=[]
    for j in range(n):
        k=len(piv)
        i=next((i for i in range(k,len(A)) if A[i][j]),None)
        if i is None: continue
        A[k],A[i]=A[i],A[k]
        a=A[k][j]
        A[k]=[v/a for v in A[k]]
        for i in range(len(A)):
            if i!=k and A[i][j]:
                b=A[i][j]
                A[i]=[v-b*w for v,w in zip(A[i],A[k])]
        piv.append(j)
    if any(r[-1] for r in A[len(piv):]): return None
    v=[Q(0)]*n
    for i,j in enumerate(piv): v[j]=A[i][-1]
    return v

def dot(A,B):
    return sum(a*b for a,b in zip(A,B))

def values(p,xs):
    return [sum(v*x**i for i,v in enumerate(p)) for x in xs]

def prim(p):
    return [Q(0)]+[a/(i+1) for i,a in enumerate(p)]

def literal(ys,z0):
    t=Q(22,31); r=Q(341,683)
    clocks=[Q(1),1+t,1+2*t]
    head=[[Q(1),Q(0),Q(0)],[t,Q(1),Q(0)],[2*t-r,r,Q(1)]]
    g=[2*dot(row,clocks)-x*x for row,x in zip(head,clocks)]
    V=[[a**i for a in clocks] for i in range(3)]
    VT=list(map(list,zip(*V)))
    q=linear(VT,g,3)
    qc=linear(VT,[a*b for a,b in zip(g,clocks)],3)
    assert q and qc
    f=[-prod(clocks),sum(clocks[i]*clocks[j] for i in range(3) for j in range(i+1,3)),-sum(clocks),Q(1)]
    c=[z0-v for v in ys]
    mon=[[x**i for x in c] for i in range(7)]
    I0=[z0**i/(i+1) for i in range(7)]
    b=linear(mon,I0,6)
    if not b or not all(b): return None
    bx=[w*x for w,x in zip(b,c)]
    bx2=[w*x*x for w,x in zip(b,c)]
    inds=[[int(i==k) for i in range(6)] for k in (4,5)]
    r=linear(mon[:5]+inds,[I0[j+2]/(j+1) for j in range(5)]+
             [b[4]*(c[4]+c[5]*(z0-c[4]-1)),bx[5]],6)
    if not r: return None
    slots=[(i,j) for i in range(6) for j in range(i)]
    L,R=[],[]
    def eq(coef,want):
        L.append([coef(i,j) for i,j in slots]); R.append(want)
    qx,qj=values(q,c),values(prim(q),c)
    for i,xx in enumerate(c):
        eq(lambda row,col: qx[col] if i==row else 0,qj[i]-qx[i])
    for j,xx in enumerate(c):
        eq(lambda row,col:b[row] if col==j else 0,b[j]*(z0-xx-1))
        eq(lambda row,col:bx[row] if col==j else 0,r[j]-bx[j])
    for row in (bx2,r):
        for p in (qc,f):
            px,pj=values(p,c),values(prim(p),c)
            eq(lambda i,j:row[i]*px[j],dot(row,[v-w for v,w in zip(pj,px)]))
    m=linear(L,R,15)
    if m is None: return None
    B=[[Q(int(i==j)) for j in range(6)] for i in range(6)]
    for (i,j),v in zip(slots,m): B[i][j]=v
    A=[p+[Q(0)]*6 for p in head]
    for i,x0 in enumerate(c):
        a=linear(V,[x0**(j+1)/(j+1)-dot(B[i],mon[j]) for j in range(3)],3)
        assert a is not None
        A.append(a+B[i])
    return [[v/z0 for v in row] for row in A],[Q(0)]*3+b

@lru_cache(None)
def size(T): return 1+sum(map(size,T))
@lru_cache(None)
def density(T): return size(T)*prod(map(density,T))
@lru_cache(None)
def trees(n):
    if n==1: return ((),)
    ts=tuple(T for j in range(1,n) for T in trees(j))
    def choose(start,left):
        if not left: yield ()
        for i in range(start,len(ts)):
            T=ts[i]; rem=left-size(T)
            if rem<0: break
            for r in choose(i,rem): yield (T,)+r
    return tuple(choose(0,n-1))
def exact(T):
    A,b=T
    @lru_cache(None)
    def stage(t): return tuple(prod(dot(A[i],stage(w)) for w in t) for i in range(9))
    def defect(t): return density(t)*dot(b,stage(t))-1
    all_t=[t for j in range(1,8) for t in trees(j)]
    assert len(set(all_t))==85
    if any(defect(t) for t in all_t): return None
    for t in trees(8):
        if defect(t): return t,defect(t)
    return "through eight"

def main():
    cli=argparse.ArgumentParser()
    cli.add_argument('position',choices=['first','second'])
    cli.add_argument('--height',type=int,default=80)
    args=cli.parse_args()
    L,fs=chronology(S.Rational(22,31),S.Rational(11),d)
    P0=[g for g,e in fs[1] if S.degree(g,u)==2][0]
    F=S.Poly(P0.subs(u,11 if args.position=='first' else d),z,d).primitive()[1]
    dz,dd=F.degree_list()
    terms={(i,j):int(c) for (i,j),c in F.terms()}
    def project(a,b):
        out=[0]*(dz+1)
        for (i,j),v in terms.items():
            out[i]+=v*a**j*b**(dd-j)
        return fmpz_poly(out)
    primes=list(S.primerange(11,60))
    allowed={}
    for p in primes:
        perm=set()
        for a in range(p+1):
            g=nmod_poly(project(a,int(a!=p)).coeffs(),p)
            if g.degree()!=dz or g.roots():
                perm.add(a)
        allowed[p]=perm
    before=after=projected=0
    B=args.height
    for b0 in range(1,B+1):
        for a0 in range(-B,B+1):
            if gcd(a0,b0)!=1 or a0==11*b0 or (a0==b0 and args.position=="second"): continue
            before+=1
            if any((a0*pow(b0,-1,p)%p if b0%p else p) not in allowed[p] for p in primes):
                continue
            after+=1
            g=project(a0,b0)
            assert g
            co,fs=g.factor()
            assert g==co*prod((p**k for p,k in fs),start=fmpz_poly([1]))
            for p,_ in fs:
                if p.degree()!=1 or not p[0]:continue
                zc=Q(-int(p[0]),int(p[1]))
                dc=Q(a0,b0)
                uc=Q(11) if args.position=='first' else dc
                if uc==1: continue
                projected+=1
                tag={u:S.Rational(uc),z:S.Rational(zc),d:S.Rational(dc)}
                vv=[rational(f.subs(tag)) for f in L]
                if not vv[0]: print('special zero moment',dc,zc,uc); continue
                y3=vv[1]/vv[0]
                y1,y2=zc-11,zc-dc
                poly=(y-1)*(y-S.Rational(uc))*(y-S.Rational(y3))*(y-S.Rational(y1))*(y-S.Rational(y2))
                den=I(poly).subs(z,zc)
                if not den: continue
                y4=rational(I(poly,1).subs(z,zc)/den)
                ys=[y1,y2,y3,y4,uc,Q(1)]
                if len(set(ys))!=6:continue
                T=literal(ys,zc)
                V=exact(T) if T is not None else None
                print('candidate',dc,zc,uc,ys,V,flush=True)
                if V is not None: print(T); return
    print('Rational d height',B,':',before,'eligible;',after,'factored;',projected,'nonzero projected rational z.')
if __name__=='__main__': main()

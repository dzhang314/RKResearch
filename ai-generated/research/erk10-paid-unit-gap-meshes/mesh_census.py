#!/usr/bin/env python3
"""Exact S-unit mesh census for two regular canonical doubled-prefix reverse charts."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import permutations
from math import prod
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "erk10-paid-doubled-prefix"))
from horizons import units, unit as smooth_unit

Q = F
Z,O=Q(0),Q(1)
s_unit_solutions=units

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def hull(xs):
    v=[xs[0]*0+1]
    for x in xs:
        u=[0]*(len(v)+1)
        for j,t in enumerate(v):u[j]-=t*x;u[j+1]+=t
        v=u
    return tuple(v)
def mu(p):return sum(c/(j+1)for j,c in enumerate(p))
def lin(M,b,n):
    A=[list(row)+[x]for row,x in zip(M,b)]
    P={}
    for r in A:
        for j in range(n):
            a=r[j]
            if not a:continue
            if j not in P:
                P[j]=[x/a for x in r]
                break
            r=[x-a*y for x,y in zip(r,P[j])]
        else:
            if r[-1]:return
    x=[0]*n
    for j in sorted(P,reverse=True):x[j]=P[j][-1]-dot(P[j][j+1:n],x[j+1:])
    return x,len(P)

def coeff(p,q,r):
    return (q**4*(r-p), q*r*r*(p-q)*(3*q-2*r),
        p*q*(p*p*q+2*p*p*r+p*q*q-6*p*q*r+2*q*q*r),
        p*r*r*(p-q)*(2*r-3*p), p**4*(r-q))
def E(p,q,r,v1,v2,v3):
    return dot(coeff(p,q,r),(v2*v2,v2*v3,v1*v2,v1*v3,v1*v1))

def scalar(sites, allowzero=False):
    mu0={x:mu(hull([v for v in sites if v!=x]))for x in sites}
    if not allowzero and not all(mu0.values()):return
    cof={x:1/prod(x-y for y in sites if y!=x)for x in sites}
    W={x:mu0[x]*cof[x]for x in sites}
    assert all(sum(w*x**k for x,w in W.items())==1/(next(iter(W))*0+k+1) for k in range(10))
    return W,cof,mu0

def inverse(T):
 n=len(T)
 L=[lin(T,[F(int(i==j))for i in range(n)],n)for j in range(n)]
 if any(p is None for p in L):return
 if any(p[1]!=n for p in L):return
 return tuple(zip(*(p[0]for p in L)))
def shape(nodes,head):
 W,Q,P=scalar(tuple(nodes))
 cof={x:Q[x]*(x-1)for x in nodes if x not in (0,1)}
 y={x:1-x for x in nodes}
 a,b,c=head
 u0=-W[a]*y[a]**2/(2*cof[a])
 U={x:u0*cof[x] for x in cof};U[F(1)]=F(0)
 rst=(F(1),a,b,c)
 RZ=[{x:w*y[x]**i for x,w in W.items()}for i in range(5)]
 K={rst[0]:[F(0)]*4}
 def act(r,v):return dot(r,[v[x]for x in rst])
 K[a]=[RZ[1][a]/W[F(1)],F(0),F(0),F(0)]
 K[b]=lin([[q[F(1)],q[a]]for q in RZ[:2]],[RZ[1][b],RZ[2][b]/2+U[b]],2)[0]+[F(0)]*2
 Q=inverse([[U[x],x*U[x]] for x in(a,b)])
 yU={x:x*U[x]for x in U}
 comp=[]
 for vals in ([act(K[x],RZ[2])-RZ[3][x]/3 for x in(a,b)],[act(K[x],U)for x in(a,b)]):
  k1,k2=[dot(row,vals)for row in Q]
  comp.append({x:U[x]*(k1+k2*x)for x in U})
 G,H=comp
 B=[*RZ[:3],U]
 tar=lambda x:[RZ[1][x],RZ[2][x]/2+U[x],RZ[3][x]/3+G[x],H[x]]
 V0=lin([[a[x]for x in rst[:3]]for a in RZ[:3]],tar(c)[:3],3)
 K[c]=V0[0]+[F(0)]
 assert act(K[c],U)==H[c],(rst,c,act(K[c],U),H[c])
 VS=inverse([[rr[x]for x in rst]for rr in B])
 if VS is None:return
 Wt=set(nodes)-{F(0),*rst}
 for x in Wt:K[x]=[dot(row,tar(x))for row in VS]
 Q0={x:(act(row,RZ[3])-RZ[4][x]/4,act(row,yU))for x,row in K.items()}
 dif={}
 for x in Wt:
  de=[dot(row,[-rr[x]for rr in B])for row in VS]
  dif[x]=(act(de,RZ[3])+RZ[3][x],act(de,yU)+yU[x])
 return W,cof,Q0,dif

def polv(a,x):
 y=0
 for u in reversed(a):y=y*x+u
 return y
def modhull(nodes,p):
    cs=[1]
    for t in nodes:
        rr=[0]*(len(cs)+1)
        for j,x in enumerate(cs):
            rr[j]-=t*x;rr[j+1]+=x
        cs=[x%p for x in rr]
    return cs
def μ(xs,p):
    return sum(w*pow(j+1,-1,p)for j,w in enumerate(xs))%p
def red(a,p):
    a=Q(a)
    return a.numerator*pow(a.denominator,-1,p)%p
def modscalar(P,p):
    W,M,D={},{},{}
    for x in P:
        V=tuple(y for y in P if x!=y)
        D[x]=pow(prod(x-y for y in V),-1,p)
        M[x]=μ(modhull(V,p),p)
        W[x]=M[x]*D[x]%p
    assert all(sum(W[x]*pow(x,j,p)for x in P)%p==pow(j+1,-1,p)for j in range(10))
    return W,M,D
def graph():
    U=tuple(sorted(s_unit_solutions()))
    N=len(U)
    G=[0]*N
    for i in range(N):
        for j in range(i+1,N):
            if smooth_unit(U[i]-U[j]):
                G[i]|=1<<j;G[j]|=1<<i
    print('Graph',N,'vertices',sum(x.bit_count()for x in G)//2,'edges',flush=True)
    return U,G

def enum(U,G,num):
    def dfs(ch,left,n):
        if n==0:
            yield ch;return
        while left.bit_count()>=n:
             x=(left & -left).bit_length()-1
             left^=1<<x
             yield from dfs((*ch,x),left&G[x],n-1)
    yield from (tuple(U[i]for i in k) for k in dfs((),(1<<len(U))-1,num))


def product(p,q):
    out=[Z]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):
            out[i+j]+=a*b
    return out

def add(p,q):
    out=[Z]*max(len(p),len(q))
    for xs in (p,q):
        for j,x in enumerate(xs):out[j]+=x
    return out

def scale(k,p):return [k*x for x in p]

def aggregate(P):
    M={x:mu(hull(tuple(y for y in P if y!=x))) for x in P}
    D={x:1/prod(x-y for y in P if y!=x) for x in P}
    W={x:M[x]*D[x] for x in P}
    assert all(sum(w*x**j for x,w in W.items())==O/(j+1)for j in range(10))
    return M,W,D

def hour(P,M,W,D):
    for A,B in permutations((p for p in P if p not in (0,1)),2):
        if not W[1] or not W[A] or not W[B]:continue
        p,q=1-A,1-B
        if M[A]*p*(3*q-2*p)!=M[B]*q*q:continue
        u,v=-1/M[A],-1/M[B]
        beta=(v-u)/(q-p);alpha=u-beta*p
        # Hull([1]*k)=(X-1)^k, so negate odd powers to evaluate in y=1-X.
        YY=[scale((-1)**k,hull([O]*k))if k else [O] for k in range(5)]
        L=add(add(scale((p+q)/3,YY[3]),scale(-p*q/2,YY[2])),scale(-Q(1,4),YY[4]))
        R=add(scale(alpha/2,YY[2]),scale(beta/3,YY[3]))
        for h in sorted(set(P)-{0,1,A,B}):
            y=1-h
            rK=W[h]*y*(y-p)*(y-q)
            rV=(h-1)*D[h]-W[h]*y*(alpha+beta*y)
            if not(rK or rV):continue
            yield A,B,h,add(scale(rK,R),scale(-rV,L))

def grids(k):
    U,G=graph()
    stat=Counter()
    seen=set()
    for P in enum(U,G,k-2):
        stat["cliques"]+=1
        R=tuple(sorted(1-x for x in P))
        if R<P:continue
        stat["reflection representatives"]+=1
        pts=tuple(sorted((Z,O,*P)))
        if k==9 and mu(hull(pts)):continue
        stat["precision nine representatives"]+=1
        for omega in (pts,tuple(sorted(1-x for x in pts))):
            if omega not in seen:
                seen.add(omega)
                yield omega
    print("scalar grids",k,dict(stat),flush=True)

def repeated():
    stat=Counter()
    for P in grids(9):
        stat["meshes"]+=1
        M,W,D=aggregate(P)
        for A,B,h,density in hour(P,M,W,D):
            oth=set(P)-{Z,O,A,B,h}
            stat["head donor"]+=1
            for xi,first in permutations(sorted(oth),2):
                d,e=sorted(oth-{xi,first})
                f=hull((Z,xi,d,e))
                z=product(f,density)
                q0,q1=mu(z),mu([Z]+z)
                a,b=xi*Q(2,3),xi*Q(4,5)
                x,y=polv(f,a),Q(625,648)*polv(f,b)
                m0,m1=x-y,a*x-b*y
                if m0*q1!=m1*q0:continue
                stat["pressure passed"]+=1
                if not(m0 or m1)and(q0 or q1):
                    stat["blind-both false"]+=1
                    continue
                print("repeated candidate survives",A,B,h,xi,first,d,e,q0,q1,m0,m1)
                stat["continued"]+=1
    print("repeated", dict(stat),flush=True)
    assert stat==Counter({"meshes":222,"head donor":250,"pressure passed":6,"blind-both false":6})

@cache
def modhead(nodes,p):
    W,mu,_=modscalar(nodes,p)
    c={x:(mu[x]*pow(x-1,-1,p))%p for x in nodes if x not in (0,1)}
    out=[]
    for a,b,z in permutations(c,3):
        if E(1-a,1-b,1-z,c[a],c[b],c[z])%p==0:out.append((a,b,z))
    return tuple(out)
def heads(P):
    m={red(x,11):x for x in P}
    cand=modhead(tuple(sorted(m)),11)
    if not cand:return ()
    m1={x:red(x,13)for x in P}
    held=set(modhead(tuple(sorted(m1.values())),13))
    out=[]
    for v in cand:
       h=tuple(m[i]for i in v)
       if tuple(m1[i]for i in h) in held:out.append(h)
    return out

def distinct():
    stat=Counter()
    for P in grids(10):
        stat["meshes"]+=1
        hh=heads(P)
        if not hh:continue
        WQ=scalar(P)
        if WQ is None:continue
        W,D,Y=WQ
        v={x:Y[x]/(x-1)for x in Y if x not in (0,1)}
        for h in hh:
           a,b,e0=h;stat['survive mod 11 and 13']+=1
           if E(1-a,1-b,1-e0,v[a],v[b],v[e0]):continue
           stat['exact entrance']+=1
           pp=shape(P,h)
           if pp is None:continue
           W,C,Qb,delta=pp
           oth=set(P)-{0,1,*h}
           for xi,x4,x5 in permutations(sorted(oth),3):
             x6,x7=sorted(oth-{xi,x4,x5})
             z1,z2=delta[x4]
             F=hull((Z,xi,x6,x7))
             u4={x:polv(F,x)for x in Qb}
             QV={x:z1*b-z2*a for x,(a,b)in Qb.items()}
             q0=sum(QV[x]*q for x,q in u4.items())
             q1=sum(QV[x]*x*q for x,q in u4.items())
             ca,cb=xi*Q(2,3),xi*Q(4,5)
             p0=polv(F,ca);p1=Q(625,648)*polv(F,cb)
             l0=p0-p1;l1=ca*p0-cb*p1
             if q0*l1!=q1*l0:continue
             if not(l0 or l1)and(q0 or q1):stat['blind-both false']+=1;continue
             print("surviving distinct candidate", (O,*h,x4,x5,x6,x7,xi),flush=True)
             stat["nonblind survivors"]+=1
    print("distinct",dict(stat),flush=True)
    assert stat["meshes"]==55935
    assert stat["exact entrance"]==478
    assert stat["blind-both false"]==104
    assert not stat["nonblind survivors"]

if __name__=='__main__':
    todo=set(sys.argv[1:])
    if not todo or "nine" in todo:repeated()
    if not todo or "ten" in todo:distinct()

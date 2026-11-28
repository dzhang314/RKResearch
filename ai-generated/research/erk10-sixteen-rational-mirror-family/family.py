#!/usr/bin/env python3
"""Deterministic exact rational ERK10 mirrored construction.

The rank-three terminal equation is made linear by fixing one evaluation site.
Each returned tableau is rational; the verifier reads its uncompressed trees.
"""
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict,Counter
from functools import cache
from math import prod,lcm
from pathlib import Path
import argparse,sys,json
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parent/'erk10-sixteen-late-helper-primes'),str(HERE.parent/'erk10-late-helper')]
from build import prefix as old_prefix
import replay as pol

Z,O=Q(0),Q(1)
C=Q(1,2); A=Q(2,3); B=Q(1,3)
Y=[O,-O]
def paid(x):
    n=Q(x).denominator
    for p in (2,3,5,7):
        while n%p==0:n//=p
    return n==1

def choose(t,case,anchor,paid_clocks=False):
    if t in (0,1,2):
        return
    v=t*(12*t*t-45*t+40)/(15*(t-2)**2)
    if v in (0,1,2,t,Q(2,3)):
        return
    alpha,beta=v/t,2/t
    c,e=(beta,alpha)if anchor=='b' else (alpha,beta)
    if c in (0,1)or e in (0,1)or c==e:
        return
    if case==0:
        xi=C;E=c*C;D=1-E
        V=(2*E-1)**2
    elif case==1:
        xi=C/c;E=C;D=1-xi
        V=(2*xi-1)**2
    elif case==2:
        if c==-1:return
        xi=1/(1+c);E=1-xi;D=C
        V=(2*xi-1)**2
    if V in (0,1,Q(1,9))or len({Z,O,A,B,xi,E,D})!=7:return
    r=xi*e
    H=pol.hull((Z,xi,E,r))
    if paid_clocks and not all(paid(u)for u in (xi,E,D,r,xi/t)):
        return
    I=2*V/15-Q(2,35);J=2*V/35-Q(2,63)
    if not I:return
    m=(Q(1,9)-J/I)/8
    QY=pol.mul(pol.pw(Y,2),pol.add(pol.scale(Q(-1,4),pol.pw(pol.add(Y,[Q(-2,3)]),2)),[-m]))
    HP=pol.mul(H,QY)
    k0=pol.mu(HP);k1=pol.mu(HP,1)
    if not k0:return
    R=k1/k0
    if paid_clocks and not paid(R):return
    raw=(O,A,B,A,1-R,D,R,E,xi)
    if len({Z,*raw})!=9 or R==r:return
    # The unmatched evaluation lies off all four blind-test roots.
    assert r not in (Z,xi,E,R)
    return raw,(r,m,R)

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))

def solve(A,b,n):
    out={}
    for idx,rr in enumerate(A):
        r=list(map(Q,rr))+[Q(b[idx])]
        for j in range(n):
            v=r[j]
            if not v:continue
            if j not in out:
                out[j]=[x/v for x in r]
                break
            r=[a-v*b for a,b in zip(r,out[j])]
        else:
            if r[-1]:return
    x=[Z]*n
    for j in sorted(out,reverse=True):
        row=out[j];x[j]=row[-1]-dot(row[j+1:n],x[j+1:n])
    assert all(dot(r,x)==v for r,v in zip(A,b))
    return x,len(out)

def scalar(sites):
    nodes=tuple(sorted(set(sites)))
    assert len(nodes)==9
    W={};C0={}
    for a in nodes:
        off=tuple(x for x in nodes if a!=x)
        v=pol.mu(pol.hull(off))
        if not v:return
        C0[a]=1/prod(a-x for x in off)
        W[a]=v*C0[a]
    assert all(sum(v*x**j for x,v in W.items())==1/Q(j+1)for j in range(10))
    return W,C0

@cache
def prefix(t):
    for p in (1009,101,103,107,109,113,127,137,139,149,1543):
        try:return old_prefix(t,p,defaultdict(list))
        except (ValueError,AssertionError):continue

def shape(c,W,C0,pad=Q(1,2)):
    p,q=1-A,1-B
    yi=[1-x for x in c]
    w=[W[x] if j not in (1,3)else W[x]*(pad if j==1 else 1-pad)for j,x in enumerate(c)]
    if not all(w):return
    U=[Z]*9;U[1]=-w[1]*p*p/2;U[3]=-U[1]
    V=[Z]+[(x-1)*C0[x]*(w[j]/W[x])for j,x in enumerate(c)if j]
    Ms=[[w*y**j for w,y in zip(w,yi)]for j in range(5)]
    gg=w[2]*q*q*p/2-w[2]*q**3/3
    hh=-w[2]*q*q*p/4
    ag=gg/V[2];ah=hh/V[2]
    ug=(-w[1]*p**3/3-ag*V[1])/U[1];uh=-ah*V[1]/U[1]
    G=[ag*v+ug*u for v,u in zip(V,U)];H=[ah*v+uh*u for v,u in zip(V,U)]
    assert all(not sum(r*x**j for r,x in zip(U,c))for j in range(1,8))
    assert all(not sum(r*x**j for r,x in zip(V,c))for j in range(1,7))
    target=lambda i:[Ms[1][i],Ms[2][i]/2+U[i],Ms[3][i]/3+G[i],H[i]]
    rows=[*Ms[:3],U]
    K=[[Z]*9 for _ in range(9)]
    for i in range(1,9):
       n=min(i,4)
       ans=solve([r[:n]for r in rows[:n]],target(i)[:n],n)
       if not ans or ans[1]!=n:return
       K[i][:n]=ans[0]
       assert [dot(K[i],r)for r in rows]==target(i),(i,c)
    Vec={}
    for j in range(4,8):
       z=solve([r[:4]for r in rows],[-rr[j]for rr in rows],4)
       assert z and z[1]==4
       t=z[0]+[Z]*5;t[j]=O
       assert all(not dot(t,r)for r in rows)
       Vec[j]=t
    return w,K,Ms,V,rows,target,Vec

def construct(t,c,quad=None,pad=Q(1,2)):
    if quad is None:
        quad=scalar((Z,*c))
    if quad is None:return
    W,C0=quad
    z=shape(c,W,C0,pad=pad)
    if z is None:return
    w,K,Ms,V,RR,tgt,Vec=z
    d=prefix(t)
    if d is None:return
    A,Pi,H=d
    scale=c[-1]/t
    A=[[x*scale for x in row]for row in A]
    Pi=[[x/scale**k for x in r]for k,r in enumerate(Pi)]
    H=[[x/scale**k for k,x in enumerate(r)]for r in H]
    P=[[pol.ev(r,x)for x in c]for r in H]
    taps=[(i,j)for i in range(5,8)for j in range(4,i)]
    Q0=(Ms[3],V)
    Pay=[];RHS=[]
    for a0,v in enumerate(Q0):
        k=[dot(r,v)-(Ms[4][i]/4 if a0==0 else 0)for i,r in enumerate(K)]
        for test in P:
            RHS.append(-dot(test,k))
            Pay.append([test[i]*dot(Vec[j],v)for i,j in taps])
    sol=solve(Pay,RHS,len(taps))
    if not sol:return
    E,rank=sol
    for (i,j),v in zip(taps,E):
       K[i]=[x+v*y for x,y in zip(K[i],Vec[j])]
    assert all([dot(r,q)for q in RR]==tgt(i)and not any(r[i:])for i,r in enumerate(K))
    for k0,v in enumerate(Q0):
       col=[dot(r,v)-(Ms[4][i]/4 if not k0 else 0)for i,r in enumerate(K)]
       assert all(not dot(r,col)for r in P)
    C=c[::-1];n=9
    for i,x in enumerate(C):
       high=[K[n-1-j][n-1-i]if j<i else Z for j in range(n)]
       integ=[x**(k+1)/(k+1)-dot(high,[u**k for u in C])for k in range(5)]
       top=[dot(integ,[r[h]for r in Pi])for h in range(8)]
       if i==0:
          assert top==A[7]+[Z]
       else:
          top[7]+=high[0]
          A.append(top+high[1:i])
    b=[W[Z]]+[Z]*6+w[::-1]
    assert len(A)==len(b)==16 and all(len(r)==i for i,r in enumerate(A))
    defect=11*sum(w*sum(r)**10 for w,r in zip(b,A))-1
    if not defect:return
    D=lcm(*(x.denominator for rr in A+[b]for x in rr))
    return {'A':[list(map(str,r))for r in A],'b':list(map(str,b)),'denominator':str(D),
            'theta':str(t),'raw':list(map(str,c)),'next_failure_tree':[[]]*10,
            'next_failure_value':str(defect),'rank':rank}

def make(t,case,anchor):
    u=choose(t,case,anchor)
    if u is None:return
    c,_=u
    return construct(t,c)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--theta',default='-1/2')
    ap.add_argument('--case',type=int,default=2,choices=(0,1,2))
    ap.add_argument('--anchor',default='b',choices=('a','b'))
    ap.add_argument('--emit',type=Path)
    a=ap.parse_args()
    ans=make(Q(a.theta),a.case,a.anchor)
    assert ans is not None
    txt=json.dumps(ans,indent=2)+'\n'
    if a.emit:a.emit.write_text(txt)
    else:print(txt,end='')
if __name__=='__main__':
    main()

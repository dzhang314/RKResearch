#!/usr/bin/env python3
"""Exact paid-nullspace projection with one or two potentially dirty high rows."""
from functools import cache
from itertools import product,islice
import numpy as np
import pressure as f
from sympy import primerange
import sys
from pathlib import Path
if len(sys.argv)<2:
    sys.argv.append(str(Path(__file__).parent.parent/'erk10-stepanov-five-opening'/
                        'stepanov15-source.txt'))
def choose():
    D=[int(r.split()[-1])for r in open(sys.argv[1])]
    for p in primerange(23,5000):
        if any((63*d)%p==0 for d in D):continue
        R={i*i%p:i for i in range(p)}
        if 3 not in R or 7 not in R:continue
        for y in (R[7],-R[7]%p):
            if (147+42*y)%p not in R:continue
            x,z=R[3],R[(147+42*y)%p]
            c,b,A=f.read(p,x,y,z)
            B=[line[6:]for line in A[6:]];c,b=c[6:],b[6:]
            M=[[(u**(k+1)*f.inv(k+1)-sum(row[j]*c[j]**k for j in range(9)))%p for k in range(1,4)] for row,u in zip(B,c)]
            if not f.det([r[:2]for r in M[:2]]):continue
            a,g=f.solve([r[:2]for r in M[:2]],[-r[2]%p for r in M[:2]])
            delta=(g*g-4*a)%p
            if delta not in R or delta==0:continue
            l=(R[delta]-g)*f.inv(2)%p
            r=(-R[delta]-g)*f.inv(2)%p
            if not l or not r or l==r or len(set(c))<5:continue
            assert all(f.dot(row,[a,g,1])==0 for row in M)
            yield p,x,y,z,l,r,c,b,B

def rank(X):
    R=np.array(X,dtype=np.int64)%f.P
    nr,nc=R.shape;ii=0;rows=list(range(nr));cols=[]
    for k in range(nc):
        pp=np.flatnonzero(R[ii:,k])
        if not len(pp):continue
        j=ii+pp[0]
        R[[ii,j]]=R[[j,ii]];rows[ii],rows[j]=rows[j],rows[ii]
        R[ii,k:]=(R[ii,k:]*f.inv(R[ii,k]))%f.P
        ids=np.arange(ii+1,nr)
        R[ids,k:]=(R[ids,k:]-R[ids,k,None]*R[ii,k:])%f.P
        cols.append(k);ii+=1
        if ii==nr:break
    return ii,rows[:ii],cols

@cache
def trees(n):
    if n==1:return ((),)
    P=[(j,t)for j in range(1,n)for t in trees(j)]
    def rec(m,i):
        if m==0:yield ();return
        for k in range(i,len(P)):
            j,t=P[k]
            if j>m:break
            for out in rec(m-j,k):yield (t,)+out
    return tuple(rec(n-1,0))
@cache
def size(t):return 1+sum(size(x)for x in t)
@cache
def factorial(t):
    z=size(t)
    for u in t:z*=factorial(u)
    return z

def evaluate(p,x,y,z,p0,q0,c,b,B,dirty=(0,),split=False):
    f.P=p
    links=[(i,j)for i in range(9)for j in range(i)]
    pair=[(0,6),(1,7),(2,3),(4,5)]
    free=[(i,j)for i,j in pair if i not in dirty] if split else []
    N=2+len(links)+len(dirty)+len(free)
    assert not any(b[i] for i in dirty)
    class J:
        def __init__(self,v,d=None):
            self.v=int(v)%p;self.d=np.zeros(N,dtype=np.int64)if d is None else d%p
        def __add__(self,y):
            if not isinstance(y,J):y=J(y)
            return J(self.v+y.v,self.d+y.d)
        __radd__=__add__
        def __neg__(self):return J(-self.v,-self.d)
        def __sub__(self,y):return self+-y
        def __rsub__(self,y):return -self+y
        def __mul__(self,y):
            if not isinstance(y,J):y=J(y)
            return J(self.v*y.v,self.v*y.d+y.v*self.d)
        __rmul__=__mul__
        def inv(self):
            r=f.inv(self.v)
            return J(r,-r*r*self.d)
        def __truediv__(self,y):return self*(y.inv()if isinstance(y,J)else f.inv(y))
        def __rtruediv__(self,y):return self.inv()*y
        def __pow__(self,k):
            if k==0:return J(1)
            if k==1:return self
            z=self**(k//2)
            return (z*z)*(self if k%2 else 1)
    j=0
    def var(u):
        nonlocal j
        e=np.zeros(N,dtype=np.int64);e[j]=1;j+=1
        return J(u,e)
    P,Q=var(p0),var(q0)
    T=[[J(0)for j in range(9)]for i in range(9)]
    for i,z in links:T[i][z]=var(B[i][z])
    u={d:var(0)for d in dirty}
    w=list(map(J,b))
    for i,l in free:
        a=var(w[i].v)
        w[l]=w[l]+w[i]-a;w[i]=a
    assert j==N
    o=2*P/3; e=J(2)/15
    lP=3*P/4
    lQ=3*Q**2*(3*P-2*Q)/(4*P**2)
    kQ=(Q**2/2-lQ*o)/P
    A=[[],[e],[o-o**2/(2*e),o**2/(2*e)],[P-lP,J(0),lP],
       [Q-kQ-lQ,J(0),lQ,kQ]]
    A=[g+[J(0)]*(14-len(g))for g in A]
    local=[]
    for i,ci in enumerate(c):
        W=[J(ci**(j+1)*f.inv(j+1))-sum(a*(b**j%p)for a,b in zip(T[i],c))
            -u.get(i,0)*o**j for j in range(4)]
        aP=(W[2]-Q*W[1])/(P*(P-Q))
        aQ=(W[2]-P*W[1])/(Q*(Q-P))
        A.append([W[0]-aP-aQ,J(0),u.get(i,J(0)),aP,aQ]+T[i])
        local.append(W[3]-aP*P**3-aQ*Q**3)
    w=[J(1)/30]+[J(0)]*4+w
    av=np.array([[d.v for d in r]for r in A],dtype=np.int64)
    ad=np.array([[d.d for d in r]for r in A],dtype=np.int64)
    bv=np.array([v.v for v in w],dtype=np.int64)
    bd=np.array([v.d for v in w],dtype=np.int64)
    @cache
    def diag(t):
        V=np.ones(14,dtype=np.int64)
        D=np.zeros((14,N),dtype=np.int64)
        for u in t:
            w,v=apply(u)
            D=(D*w[:,None]+V[:,None]*v)%p
            V=(V*w)%p
        return V,D
    @cache
    def apply(t):
        v,d=diag(t)
        return av@v%p,(av@d+np.einsum('ijx,j->ix',ad,v))%p
    def conditions(k):
        rows=[];vals=[]
        for t in trees(k):
            v,d=diag(t)
            rows.append(list(map(int,(bv@d+v@bd)%p)))
            vals.append(int(bv@v-f.inv(factorial(t)))%p)
        return rows,vals
    R=[list(map(int,v.d))for i,v in enumerate(local)if i not in dirty]
    assert not any(v.v for v in local)
    for n in range(1,10):
        Q,err=conditions(n); assert not any(err)
        R+=Q
    P=rank(R)[0]
    Dt=[list(map(int,local[i].d))for i in dirty]
    Dfix=rank(R+Dt)[0]
    Drough=[]
    for i in dirty:
        Drough.append(list(map(int,u[i].d)))
    DR=rank(R+Dt+Drough)[0]
    top,topR=conditions(10);TJ=rank(R+top)[0]
    ans=rank([a+[0]for a in R]+[a+[(p-v)%p]for a,v in zip(top,topR)])[0]
    print(f'p={p}, donor orientation {p0,q0}, dirty={dirty}, splits={split}: '
          f'n={N}, paid rank={P}, dirty cubic direction={Dfix-P}, '
          f'with rough={DR-P}, full top rank={TJ}, augmented rank={ans}, '
          f'failed residuals mod p={sum(bool(k)for k in topR)}',flush=True)
    return R,Dt,Drough,top,topR
if __name__=='__main__':
    for t in islice(choose(),2):
        p,x,y,z,l,r,c,b,B=t
        B0,c0,b0,H0,e0=f.high(f.read(p,x,y,z)[2],f.read(p,x,y,z)[0],f.read(p,x,y,z)[1])
        assert H0[4][0] and H0[4][1]
        print('exact radical reduction:',p,x,y,z,'dirty candidates',c0[:2],'d1 residues',H0[4][:2])
        for d,s in product([(0,),(1,),(0,1)],[False,True]):
            evaluate(*t,dirty=d,split=s)
        evaluate(p,x,y,z,r,l,c,b,B,dirty=(0,),split=True)

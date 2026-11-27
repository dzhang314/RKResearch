#!/usr/bin/env python3
"""Degree-preserving splitting-algebra screens; every matrix calculation is exact mod p."""
import itertools as it
import sys
import numpy as np
from sympy import Poly, primerange, symbols
from prior_field import seed, first_port, shifted_second, irreducible, simple

X=symbols("X")
P4=(1,-20,90,-140,70)
P5=(-1,30,-210,560,-630,252)
P=None
def eye(n): return np.eye(n,dtype=np.int64)
def zeros(n): return np.zeros((n,n),dtype=np.int64)
def mul(a,b): return (a@b)%P
def inv(A,get=True):
    n=len(A); B=np.hstack([A.copy()%P,eye(n)]) if get else A.copy()%P
    d=1
    for j in range(n):
        I=np.flatnonzero(B[j:,j])
        if not len(I): return None if get else 0
        i=j+I[0]
        if j!=i:
            B[[i,j]]=B[[j,i]]
            d=-d
        v=int(B[j,j]); d=d*v%P
        B[j,j:]=(B[j,j:]*pow(v,-1,P))%P
        if get:
            ii=np.r_[np.arange(j),np.arange(j+1,n)]
        else:
            ii=np.arange(j+1,n)
        B[ii,j:]=(B[ii,j:]-B[ii,j,None]*B[j,j:])%P
    return B[:,n:] if get else d%P
def times(coeffs,x):
    O=eye(len(x))
    y=zeros(len(x))
    for t in coeffs[::-1]: y=(mul(y,x)+t*O)%P
    return y
def peval(coeffs,x):
    y=zeros(len(x))
    for t in coeffs[::-1]: y=(mul(y,x)+t)%P
    return y
def pmul(a,b):
    c=[zeros(len(a[0])) for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]=(c[i+j]+mul(x,y))%P
    return c
def divlin(a,r):
    q=[zeros(len(r)) for _ in range(len(a)-1)]
    q[-1]=a[-1]
    for j in reversed(range(len(q)-1)): q[j]=(a[j+1]+mul(r,q[j+1]))%P
    R=(a[0]+mul(r,q[0]))%P
    assert np.all(R==0)
    return q
def primitive(a,x):
    O=eye(len(x)); Z=zeros(len(x))
    return peval([Z]+[c*pow(i+1,-1,P)%P for i,c in enumerate(a)],x)
def integral(a): return sum(c*pow(i+1,-1,P) for i,c in enumerate(a))%P
def companion(L):
    d=len(L); n=len(L[0]); O=eye(n)
    M=zeros(d*n)
    for j in range(d-1): M[(j+1)*n:(j+2)*n,j*n:(j+1)*n]=O
    for j in range(d): M[j*n:(j+1)*n,(d-1)*n:d*n]=-L[j]
    return M%P

def geometry(v,w):
    Z=lambda t:Poly(t,X,modulus=P)
    p4=lambda B:sum((u*(B**j) for j,u in enumerate(P4)),Z(0))
    p5=lambda B:sum((u*(B**j) for j,u in enumerate(P5)),Z(0))
    a,b=Z(1-v*X),Z(1-w*X)
    d=(p5(a)*p4(b)-p4(a)*p5(b)).exquo(Z(X))
    if d.degree()!=8: return
    d=d.monic()
    G=companion([np.array([[int(d.nth(j))]])%P for j in range(8)])
    O=eye(8); a=(O-v*G)%P; b=(O-w*G)%P
    p4a=times(P4,a); p5a=times(P5,a); Ii=inv(p4a)
    if Ii is None: return
    lam=(-mul(p5a,Ii))%P
    hull=[(P5[j]*O+(P4[j] if j<5 else 0)*lam)*pow(252,-1,P)%P for j in range(6)]
    L=divlin(divlin(hull,a),b)
    R=companion(L[:-1])
    L=[np.kron(eye(3),u)%P for u in L]
    S=companion([(L[1]+mul(L[2],R)+mul(R,R))%P,(L[2]+R)%P])
    r=np.kron(eye(2),R)
    G,a,b,hull2=[np.kron(eye(6),v) for v in [G,a,b,lam]]
    u=(-np.kron(eye(2),L[2])-r-S)%P
    s=S
    O=eye(48)
    hull=[(P5[j]*O+(P4[j] if j<5 else 0)*hull2)*pow(252,-1,P)%P for j in range(6)]
    return G,a,b,r,s,u,hull

def gates(v,w, save=None):
    ret=geometry(v,w)
    if ret is None: return
    G,a,b,r,s,u,hull=ret
    O=eye(len(G)); Z=zeros(len(G))
    test={}
    def I(name,x):
        x=x%P
        test[name]=inv(x,get=False)
        if save is not None:
            save[name]=x
    I("gamma",G)
    for nm,x in [('a',a),('b',b),('r',r)]:
        I(nm+'!=0',x)
        I(nm+'!=ghost',x-G)
        I(nm+' != 2 ± sqrt2',mul(x,x)-4*mul(G,x)+2*mul(G,G))
    for nm,x,y in [('ab',a,b),('ar',a,r),('br',b,r),('rs',r,s)]:
        I(nm+' distinct',x-y)
        I(nm+' not siblings',x+y-4*G)
    for nm,x,y in [('ab',a,b),('ba',b,a),('ar',a,r),('ra',r,a),('br',b,r),('rb',r,b),('rs',r,s)]:
        I(nm+' not AP',y-2*x+G)
    def K(*points):
        res=[O]
        for x in points: res=pmul(res,[(-x)%P,O])
        return res
    def d(x): return mul(x-G,integral(divlin(hull,x)))
    def mu(k,x): return (primitive(k,x)-mul(G,peval(k,x)))%P
    def early(k,x,y): return (mul(d(x),mu(k,x))-mul(d(y),mu(k,y)))%P
    for tag,t in [('a',a),('b',b)]:
        # t=1, protected: first and second contributing live rows, take K vanishing at r.
        k=K(t,r); k1=[Z]+k
        I('1/1-'+tag,early(k,r,s))
        I('1/1-alt-'+tag,early(k1,r,s))
        # t=2, one protected: r is the other terminal and s is earliest live.
        k=K(t,r); k1=[Z]+k
        I('2/1-'+tag,early(k,r,s))
        I('2/1-alt-'+tag,early(k1,r,s))
        # t=3, one protected: r,s are both disjoint terminals.
        I('3/1-'+tag,early(K(t,r,s),r,s))
    # t=2, both protected: r and s are first/second genuine live.
    I('2/2',early(K(a,b,r),r,s))
    # t=3, both protected: r is disjoint terminal, s earliest true live.
    I('3/2',early(K(a,b,r),r,s))
    return test

def options():
    for p in primerange(11,386):
        for z in range(p):
            try: simple(seed(p),z,p)
            except AssertionError: continue
            for v in range(p):
                try: simple(first_port(z,p),v,p)
                except AssertionError: continue
                if not v or not (3*z-v)%p: continue
                for w in range(p):
                    if not w or w==v: continue
                    try: simple(shifted_second(z,v,p),w,p)
                    except AssertionError: continue
                    yield p,z,v,w

def main(limit):
    global P
    assert all(n**3-9*n*n+18*n-6 for n in [-6,-3,-2,-1,1,2,3,6])
    simple(seed(31),11,31); irreducible(first_port(11,31),31,2)
    simple(seed(17),16,17); simple(first_port(16,17),1,17)
    irreducible(shifted_second(16,1,17),17,3)
    good={}; hit=[]
    for p,z,v,w in options():
        P=p
        if p>limit: break
        scores=gates(v,w)
        if not scores: continue
        wins=[j for j,d in scores.items() if d]
        bad=[j for j,d in scores.items() if not d]
        print(p,z,v,w,len(wins),'/',len(scores),'fail',','.join(bad),flush=True)
        for j in wins: good.setdefault(j,(p,z,v,w,scores[j]))
        if len(wins)==len(scores):
            print('FULL SINGLE PRIME',p,z,v,w,sorted(scores.items()))
            break
        if len(good)==len(scores): break
    print('Verified distinct gates:',len(good), good)
if __name__=="__main__": main(int(sys.argv[1]) if len(sys.argv)==2 else 385)

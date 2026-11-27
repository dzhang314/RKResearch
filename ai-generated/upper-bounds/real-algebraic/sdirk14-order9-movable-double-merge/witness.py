#!/usr/bin/env python3
"""Compute and rigorously isolate a 14-stage strict SDIRK order-nine witness."""
from family import front,gates,card,shift,peval,pmul
import itertools as it, json, sys
from functools import lru_cache

def prod(x,start=1):
    for u in x:start=start*u
    return start
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def powers(x,n):return [x**j for j in range(n)]
def unit(x): return x*0+1
def zero(x): return x*0
def integ(f,k=0):return sum(q/(j+k+1) for j,q in enumerate(f))
def hull(xs):
    o=unit(xs[0]);V=[o]
    for x in xs: V=pmul(V,[-x,o])
    return V
def transpose(M):return list(map(list,zip(*M)))
def eye(n,s):
    return [[unit(s) if i==j else zero(s) for j in range(n)] for i in range(n)]
def matvec(A,x):return [dot(w,x) for w in A]
def matmul(A,B):return [matvec(transpose(B),r) for r in A]
def inverse(A):
    n=len(A); C=[list(x)+y for x,y in zip(A,eye(n,A[0][0]))]
    for j in range(n):
        k=max(range(j,n),key=lambda i:strength(C[i][j]))
        C[j],C[k]=C[k],C[j]
        q=C[j][j];C[j]=[u/q for u in C[j]]
        for i in range(n):
            if i==j: continue
            q=C[i][j]
            C[i]=[t-q*u for t,u in zip(C[i],C[j])]
    return [r[n:] for r in C]
def strength(x):
    if isinstance(x,Jet):return strength(x.x)
    if isinstance(x,Ball):return abs(x.lo+x.hi)
    return abs(x)

def ap(a,d,full=False):
    x,g,f,I,m,k=front(a,d)
    zr=zero(a);o=unit(a)
    pi=inverse([powers(t,3)+[G] for t,G in zip(x,g)])[:3]
    V=[matvec(pi,[xx*gg for xx,gg in zip(x,g)])+[zr],
       [-s for s in matvec(pi,[xx**3 for xx in x])]+[o]]
    if not full:return x,g,pi,V
    mt=m.copy()
    mt[1]+=g[-1];mt[2]+=k*g[-1]
    row4=[dot(card(x[:3],i),mt) for i in range(3)]
    A=[[o,zr,zr,zr],[a-o,o,zr,zr],[x[2]-o-f,f,o,zr],row4+[o]]
    return x,g,pi,V,A

def forward(a,d,v,w,full=False):
    b=ap(a,d,full)
    x,g,pi,V=b[:4]
    e=[peval(q,v) for q in V]
    Q=[e[1]*p-e[0]*r for p,r in zip(*V)]
    if not full:return [*gates(a,d,v),shift(Q,w)]
    A=b[4]
    e0=max(range(2),key=lambda j:strength(e[j]))
    lam=shift(V[e0],w)/e[e0]
    # Use the degree <=2 dense read, including the one actual missing-degree contrast.
    muV=matvec(transpose(pi),[shift(powers0(v,j),v) for j in range(3)])
    muW=matvec(transpose(pi),[shift(powers0(w,j),w) for j in range(3)])
    pV=matvec(transpose(pi),powers(v,3))
    x=x+[v,w];g=g+[zero(a),zero(a)]
    A=[row+[zero(a),zero(a)] for row in A]
    A.append(muV+[unit(a),zero(a)])
    A.append([s-lam*t for s,t in zip(muW,pV)]+[lam,unit(a)])
    pi4=inverse([powers(t,4)+[G,t*G] for t,G in zip(x,g)])[:4]
    return x,A,pi4,Q

def powers0(x,j):
    return [zero(x)]*j+[unit(x)]

def mesh(V,W,G,H,C):
    o=unit(G)
    return [G,G+H,G+2*H,C,o-G*V,o-G*W]
def rank_gate(Y,G,V,i,j):
    eval0=[peval(u,Y[i]/G) for u in V]
    Q=integ(hull([y for k,y in enumerate(Y) if k!=i]))
    R=integ(hull([y for k,y in enumerate(Y) if k!=j]))
    L=[Q*shift(u,Y[i]/G)-R*shift(u,Y[j]/G) for u in V]
    return L[0]*eval0[1]-L[1]*eval0[0]

def eq(A,D,V,W,G,H,C):
    Y=mesh(V,W,G,H,C)
    J=hull(Y)
    _,_,_,U=ap(1+H/G,C/G)
    return [*forward(A,D,V,W),*[1000*integ(J,k) for k in range(3)],
         rank_gate(Y,G,U,0,2)]

class Ball:
    bits=384
    unit=1 << bits
    def __init__(self,l,h=None):
        self.lo=l;self.hi=l if h is None else h
        assert self.lo<=self.hi
    @classmethod
    def fromval(cls,x):
        if isinstance(x,Ball):return x
        assert isinstance(x,int)
        return Ball(x*cls.unit)
    def __add__(self,o):
        if isinstance(o,Jet):return NotImplemented
        o=Ball.fromval(o)
        return Ball(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return Ball(-self.hi,-self.lo)
    def __sub__(self,o):return self+-o
    def __rsub__(self,o):return -self+o
    def __mul__(self,o):
        if isinstance(o,Jet):return NotImplemented
        o=Ball.fromval(o);u=self.unit
        v=[a*b for a in [self.lo,self.hi] for b in [o.lo,o.hi]]
        return Ball(min(v)//u,-((-max(v))//u))
    __rmul__=__mul__
    def inv(self):
        assert self.hi<0 or self.lo>0,('division interval includes zero',repr(self))
        u=self.unit**2
        return Ball(u//self.hi,-((-u)//self.lo))
    def __truediv__(self,o):
        if isinstance(o,Jet):return NotImplemented
        return self*Ball.fromval(o).inv()
    def __rtruediv__(self,o):return self.inv()*o
    def __pow__(self,n):
        if n==0:return Ball.fromval(1)
        if n==1:return self
        q=self**(n//2)
        return q*q*(self if n%2 else 1)
    def contains0(self):return self.lo<=0<=self.hi
    def bound(self):return max(abs(self.lo),abs(self.hi))
    def bounds(self):return self.lo/self.unit,self.hi/self.unit
    def __repr__(self):return repr(self.bounds())

class Jet:
    def __init__(self,x,d=None):
        self.x=x
        self.d=[zero(x) for _ in range(7)] if d is None else d
    def __add__(self,o):
        if not isinstance(o,Jet):o=Jet(zero(self.x)+o)
        return Jet(self.x+o.x,[a+b for a,b in zip(self.d,o.d)])
    __radd__=__add__
    def __neg__(self):return Jet(-self.x,[-a for a in self.d])
    def __sub__(self,o):return self+-o
    def __rsub__(self,o):return -self+o
    def __mul__(self,o):
        if not isinstance(o,Jet):o=Jet(zero(self.x)+o)
        return Jet(self.x*o.x,[self.x*b+o.x*a for a,b in zip(self.d,o.d)])
    __rmul__=__mul__
    def inv(self):
        q=1/self.x
        return Jet(q,[-q*q*a for a in self.d])
    def __truediv__(self,o):
        if not isinstance(o,Jet):o=Jet(zero(self.x)+o)
        return self*o.inv()
    def __rtruediv__(self,o):return self.inv()*o
    def __pow__(self,n):
        if n==0:return Jet(unit(self.x))
        if n==1:return self
        q=self**(n//2)
        return q*q*(self if n%2 else 1)

def jac(vars):
    r=eye(7,vars[0])
    return [x.d for x in eq(*[Jet(t,row) for t,row in zip(vars,r)])]

C0=['0.6118477048825224','3.36573417433425','2.386361615492366','5.676314892727813',
    '0.11152160199724272','0.41619535956751535','-0.03854577848497779']

def generate(out):
    import mpmath as mp
    mp.mp.dps=145
    seed=list(map(mp.mpf,C0))
    sol=mp.findroot(eq,seed,J=lambda *t:mp.matrix(jac(t)),tol=mp.mpf(2)**(-430),maxsteps=16)
    j=jac(sol)
    P=inverse(j)
    N=312
    enc=lambda x:int(mp.nint(x*(1<<N)))
    obj={'bits':N,'center':[enc(x) for x in sol],'preconditioner':[[enc(y) for y in x]for x in P]}
    with open(out,'w') as f:json.dump(obj,f,indent=2)
    print('refined center', [mp.nstr(x,30) for x in sol])
    print('maximum rational-map residual exponent',float(mp.log(max(map(abs,eq(*sol))),2)))

def replay_root(inp):
    C=json.load(open(inp))
    e=1<<(Ball.bits-C['bits'])
    mid=[Ball(v*e) for v in C['center']]
    P=[[Ball(v*e) for v in r]for r in C['preconditioner']]
    rad=1<<(Ball.bits-160)
    box=[Ball(v.lo-rad,v.hi+rad)for v in mid]
    error=matvec(P,eq(*mid))
    jacP=matmul(P,jac(box))
    dev=[[a-b for a,b in zip(t,u)]for t,u in zip(eye(7,box[0]),jacP)]
    residual=max(u.bound() for u in error)
    lipschitz=max(sum(u.bound() for u in row)for row in dev)
    assert 2*residual<rad and 2*lipschitz<Ball.unit
    print('root interval: |center step| <= 2^%d, Lipschitz <= 2^%d, radius 2^-160'%(
          residual.bit_length()-Ball.bits,lipschitz.bit_length()-Ball.bits))
    return box

def interval_tableau(z):
    A,D,V,W,G,H,C=z
    x,F,DF,Q=forward(A,D,V,W,True)
    yc=mesh(V,W,G,H,C)
    eta=[y/G for y in yc]
    oldc,_,DR,K,R=ap(1+H/G,C/G,True)
    WT=[integ(card(yc,i)) for i in range(6)]
    sep=min(abs_bound(y-w) for y,w in it.combinations(yc,2))
    assert sep>Ball.unit//64
    assert all(v.lo>0 for v in WT)
    assert min(u.lo for u in WT)>Ball.unit//100
    bad=integ(hull(yc),3);assert not bad.contains0()
    print('clock separation >1/64; scalar weights all >1/100; next bush hull defect is',bad)
    # Chronology is first 0, second 2, then 1,3, then protected 4,5.
    ord=[0,2,1,3,4,5]
    nu=[integ(hull([y for k,y in enumerate(yc) if k!=i])) for i in range(6)]
    h=[1/prod(yc[i]-yc[j] for j in range(6) if j!=i) for i in range(6)]
    val=[[peval(p,y) for p in K] for y in eta]
    mu=[[shift(p,y) for p in K] for y in eta]
    T=eye(6,G)
    for n,i in enumerate(ord[1:4],1):
        rhs=[a-h[i]/h[0]*WT[0]*b/WT[i] for a,b in zip(mu[i],mu[0])]
        if n==1:
            j=max(range(2),key=lambda j:strength(val[0][j]))
            T[i][0]=WT[i]/WT[0]*rhs[j]/val[0][j]
        else:
            piv=[0,2]
            div=[[WT[k]*val[k][j] for k in piv] for j in range(2)]
            taps=matvec(inverse(div),[WT[i]*u for u in rhs])
            T[i][0],T[i][2]=taps
        for j in range(2):
            q=sum(T[i][k]*WT[k]*val[k][j] for k in ord[:n])-WT[i]*rhs[j]
            assert q.contains0()
    # Convert the raw-weight site operator to the normalized mean coordinates.
    T=[[WT[j]/WT[i]*T[i][j] for j in range(6)]for i in range(6)]
    # Site means are (old+fresh)/2 at four old labels, lone fresh at two ports.
    S=[zero(G)]*6
    site=[0,1,2,3]+ord
    b=[WT[i]/2 if i<4 else WT[i] for i in site]
    M=[[b[j]/WT[i] if site[j]==i else zero(G) for j in range(10)]for i in range(6)]
    unshift=[[y**(j+1)/(j+1) for j in range(3)]for y in eta]
    BS=matmul([powers(y,3)for y in eta],DR)
    Q1=matmul(unshift,DR)
    k=[r+[zero(G)]*6 for r in BS]
    Q1=[r+[zero(G)]*6 for r in Q1]
    U=[[x+y for x,y in zip(a,b)]for a,b in zip(Q1,matmul(T,[[x-y for x,y in zip(m,n)]for m,n in zip(M,k)]))]
    R=[r+[zero(G)]*6 for r in R]
    for i in ord:
        r=U[i] if i>=4 else [2*a-b for a,b in zip(U[i],R[i])]
        R.append(r)
    for i in range(10):
        assert (R[i][i]-1).contains0()
        assert (sum(R[i])-eta[site[i]]).contains0()
        assert all(R[i][j].contains0() for j in range(i+1,10))
        for j in range(i+1,10):R[i][j]=zero(G)
        R[i][i]=unit(G)
    # Weighted transpose, reverse chronology, then exact literal redirection.
    T=[[b[9-j]/b[9-i]*R[9-j][9-i] for j in range(10)]for i in range(10)]
    bx=[b[9-i] for i in range(10)]
    XX=[1/G-eta[site[9-i]] for i in range(10)]
    SX=[[u**j for j in range(4)]for u in XX]
    SXJ=[[u**(j+1)/(j+1) for j in range(4)]for u in XX]
    jx=matmul(T,SX)
    feed=matmul([[a-b for a,b in zip(r,s)]for r,s in zip(SXJ,jx)],DF)
    B=[r+[zero(G)]*10 for r in F]+[r+s for r,s in zip(feed,T)]
    Z=[zero(G)]*6+bx
    for j,p in [(7,4),(6,5)]:
        assert all((B[j][k]-B[p][k]).contains0() for k in range(16) if k not in [p,j])
        assert B[j][p].contains0() and B[p][j].contains0()
    keep=[0,1,2,3,4,5]+list(range(8,16));target={4:7,5:6}
    F14=[[(B[i][j]+(B[i][target[j]] if j in target else 0))*G
          for j in keep] for i in keep]
    b14=[Z[j]+(Z[target[j]] if j in target else 0) for j in keep]
    assert all(F14[i][j].contains0()for i in range(14)for j in range(i+1,14))
    assert all((F14[i][i]-G).contains0()for i in range(14))
    for i in range(14):F14[i][i]=G
    return F14,b14
def abs_bound(t):
    return min(abs(t.lo),abs(t.hi)) if not t.contains0() else 0

@lru_cache(None)
def trees(n):
    if n==1:return ((),)
    pool=tuple((j,t) for j in range(1,n)for t in trees(j))
    def choose(left,i):
        if left==0:yield ()
        for k in range(i,len(pool)):
            j,t=pool[k]
            if j>left:break
            for r in choose(left-j,k):yield (t,)+r
    return tuple(choose(n-1,0))
@lru_cache(None)
def size(t):return 1+sum(size(q) for q in t)
@lru_cache(None)
def factorial(t):return size(t)*prod(factorial(q) for q in t)

def all_trees(A,b,top=9):
    @lru_cache(None)
    def node(t):
        if not t:return [Ball.fromval(1)]*len(b)
        return [prod(s)for s in zip(*(prim(q)for q in t))]
    @lru_cache(None)
    def prim(t):return matvec(A,node(t))
    maxe=0;ct=0
    for j in range(1,top+1):
        e=0
        for t in trees(j):
            r=dot(b,node(t))-1/Ball.fromval(factorial(t))
            assert r.contains0(),(j,t,r)
            e=max(e,r.bound())
        print('rooted tree size',j,'count',len(trees(j)),'all deviations bounded by 2^%d'%
            (e.bit_length()-Ball.bits))
        maxe=max(e,maxe);ct+=len(trees(j))
    print('checked',ct,'total independent actual rooted conditions; max error radius 2^%d'%
          (maxe.bit_length()-Ball.bits))
    assert maxe < Ball.unit >> 90

if __name__=='__main__':
    op,path=sys.argv[1:3]
    if op=='refine':generate(path)
    else:
        assert op=='check'
        table=interval_tableau(replay_root(path))
        all_trees(*table)
        if len(sys.argv)>3:
            with open(sys.argv[3],'w') as out:
                json.dump(dict(bits=Ball.bits,A=[[[u.lo,u.hi]for u in r]for r in table[0]],
                       b=[[u.lo,u.hi]for u in table[1]]),out,indent=2)

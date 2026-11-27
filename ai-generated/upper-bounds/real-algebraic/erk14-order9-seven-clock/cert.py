#!/usr/bin/env python3
from fractions import Fraction as F
from pathlib import Path
from functools import lru_cache
from math import prod
from itertools import combinations
import json
from fixed import *
BITS=272
S=2**BITS
def lo(z):
    z=F(z)*S
    return z.numerator//z.denominator
def hi(z):return -lo(-F(z))
class Box:
    __slots__=('l','h')
    def __init__(self,a,b=None):
        if isinstance(a,Box) and b is None:self.l,self.h=a.l,a.h
        else:self.l,self.h=lo(a),hi(a if b is None else b)
        assert self.l<=self.h
    @classmethod
    def raw(cls,l,h):
        b=object.__new__(cls);b.l,b.h=l,h
        assert l<=h
        return b
    def __add__(self,b):
        if isinstance(b,Dual):return NotImplemented
        b=Box(b);return Box.raw(self.l+b.l,self.h+b.h)
    __radd__=__add__
    def __neg__(self):return Box.raw(-self.h,-self.l)
    def __sub__(self,b):
        if isinstance(b,Dual):return NotImplemented
        return self+-Box(b)
    def __rsub__(self,b):
        if isinstance(b,Dual):return NotImplemented
        return Box(b)+-self
    def __mul__(self,b):
        if isinstance(b,Dual):return NotImplemented
        b=Box(b);v=[s*t for s in (self.l,self.h) for t in (b.l,b.h)]
        return Box.raw(min(v)//S,-((-max(v))//S))
    __rmul__=__mul__
    def inv(self):
        assert self.l*self.h>0,(self.l,self.h)
        return Box.raw(S*S//self.h,-((-S*S)//self.l))
    def __truediv__(self,b):
        if isinstance(b,Dual):return NotImplemented
        return self*Box(b).inv()
    def __rtruediv__(self,b):
        if isinstance(b,Dual):return NotImplemented
        return Box(b)*self.inv()
    def __pow__(self,n):
        assert n>=0
        if n==0:return Box(1)
        if n==1:return self
        m=self**(n//2)
        return m*m*(self if n%2 else 1)
    def sign(self):
        if self.l>0:return 1
        if self.h<0:return -1
        return 0
    def char(self):
        assert self.l<=0<=self.h
    def outward(self,n=18):
        m=10**n
        return [F((self.l*m)//S,m),F(-((-self.h*m)//S),m)]
    def print(self,n=18):
        return [format(float(v),'.16g')for v in self.outward(n)]
class Dual:
    def __init__(self,a,b=0):
        if isinstance(a,Dual):self.x,self.d=a.x,a.d
        else:self.x,self.d=Box(a),Box(b)
    def __neg__(self):return Dual(-self.x,-self.d)
    def __add__(self,b):
        b=Dual(b);return Dual(self.x+b.x,self.d+b.d)
    __radd__=__add__
    def __sub__(self,b):return self+-Dual(b)
    def __rsub__(self,b):return Dual(b)+-self
    def __mul__(self,b):
        b=Dual(b);return Dual(self.x*b.x,self.x*b.d+self.d*b.x)
    __rmul__=__mul__
    def __truediv__(self,b):
        b=Dual(b);return Dual(self.x/b.x,(self.d*b.x-self.x*b.d)/b.x**2)
    def __rtruediv__(self,b):return Dual(b)/self
    def __pow__(self,n):
        return Dual(self.x**n,n*self.x**(n-1)*self.d) if n else Dual(1)
XL=F('0.49458772634688659450954002293903346')
XU=F('0.49458772634688659450954002293903347')
roots=[(F(s)-F(1,10**27),F(s)+F(1,10**27)) for s in
       ('0.071172972533863448333721659106777',
        '0.923537310308173311374945309819202',
        '0.743116233161323043913386814194211')]
@lru_cache(None)
def trees(n, lo=(0,())):
    if n==0:return ((),)
    return tuple((v,)+r for m in range(max(lo[0],1),n+1)
                 for v in trees(m-1)if (m,v)>=lo for r in trees(n-m,(m,v)))
@lru_cache(None)
def sz(t):return 1+sum(map(sz,t))
@lru_cache(None)
def fact(t):return sz(t)*prod(map(fact,t))
def rk(A):
    @lru_cache(None)
    def ph(t):
        return [prod(u[i]for u in [ex(v)for v in t]) for i in range(len(A))]
    @lru_cache(None)
    def ex(t):return [sum(a*b for a,b in zip(r,ph(t)))for r in A]
    return ph
def evalrow(v,n,divide=0):
    return [v**(j+divide)/(j+divide) if divide else v**j for j in range(n)]
def prefix(A,Pi):
    ph=rk(A)
    at=lambda r,p: sum(r[j]*p**j for j in range(len(r)))
    J=lambda r,p: sum(r[j]*p**(j+1)/(j+1)for j in range(len(r)))
    oldAt=lambda x: [at(list(r),x)for r in zip(*Pi)]
    oldJ=lambda x: [J(list(r),x)for r in zip(*Pi)]
    for loc,x in ((0,F(0)),(7,F(1)),(8,F(1,2))):
        assert oldAt(x)==[int(j==loc)for j in range(9)]
        assert oldJ(x)==A[loc]+[0]*(9-len(A[loc])),(loc,x)
    A7=A[:7]
    out=A[7]
    ph7=rk(A7)
    assert all(sum(a*b for a,b in zip(out,ph7(t)))==F(1,fact(t))
               for n in range(1,7) for t in trees(n-1))
    for n in range(1,9):
        for t in trees(n-1):
            ideal=[F(0)]*(n-1)+[F(n,fact(t))]
            e=[(ideal[j]if j<n else 0)-sum(a*b for a,b in zip(r,ph(t)))
               for j,r in enumerate(Pi)]
            e+=ideal[5:]
            assert e[0]==0
            if n<=5:assert not any(e),(n,t,e)
            elif n<=7:assert sum(e)==0
            if n==6:
                # Span of D(X)=X(X-1)(X-1/2) and D(X) X(X-1).
                D=prod_poly(([0,1],[-1,1],[F(-1,2),1]))
                G=polmul(D,[0,-1,1])
                q,r=2*e[1],e[5]
                assert e==[q*a+r*b for a,b in zip(D+[0]*2,G)]
                assert J(e,F(1))==0
    return ph
def read_prefix(file):
    j=json.loads(file.read_text())
    return [[[F(x)for x in z]for z in j[k]]for k in ['A','Pi']]
def bracket_at(x,ends):
    C=cubic(x)
    a,b=ends
    s=polval(C,a)
    assert s*polval(C,b)<0
    for _ in range(172):
        m=(a+b)/2
        t=polval(C,m)
        if not t:return Box(m)
        if s*t<0:b=m
        else:a,s=m,t
    return Box(a,b)
def verify_geometry():
    x=Box(XL,XU)
    c=cubic(x)
    dcoef=[k*c[k]for k in range(1,4)]
    boxes=[Box(a,b)for a,b in roots]
    for (a,b),u in zip(roots,boxes):
        assert polval(c,Box(a)).sign()*polval(c,Box(b)).sign()==-1
        assert polval(dcoef,u).sign()
    assert all(b.h<c.l or c.h<b.l for b,c in combinations([Box(0),Box(1),x,x/2,*boxes],2))
    for e in (XL,XU):
        T=condition(Box(e),*(bracket_at(e,r)for r in roots))
        assert T.sign()
        print('exact endpoint sign:',T.sign(),T.print(50),flush=True)
        if e==XL: sig=T.sign()
        else:assert T.sign()==-sig
    d=cubic(Dual(x,1))
    rootder=[-polval(d,u).d/polval(dcoef,u) for u in boxes]
    Y=condition(Dual(x,1),*(Dual(u,du)for u,du in zip(boxes,rootder))).d
    assert Y.sign()
    print('simple compatibility root; derivative',Y.print(),flush=True)
    return x,*boxes
def quad_symbolic():
    from itertools import zip_longest
    def add(a,b):return [x+y for x,y in zip_longest(a,b,fillvalue=0)]
    def scale(a,r):return [r*t for t in a]
    def bm(a,b):
        c=[[0] for _ in range(len(a)+len(b)-1)]
        for i,u in enumerate(a):
            for j,v in enumerate(b):c[i+j]=add(c[i+j],polmul(u,v))
        return c
    D=[20,-210,910,-1995,2303,-1323,294]
    a=polmul([1,-1],[-20,160,-498,735,-504,126])
    b=[120,-1164,4634,-9387,10080,-5418,1134]
    c=scale([36,-366,1533,-3255,3647,-2037,441],-6)
    U=bm(bm([[0],[1]],[[-1],[1]]),bm([[0,-1],[1]],[[0,F(-1,2)],[1]]))
    T=bm(U,[a,b,c,scale(D,6)])
    for k in range(3):
        E=[0]
        for j,u in enumerate(T):E=add(E,scale(u,F(1,j+k+1)))
        assert not any(E), E
    print('three cleared orthogonality polynomials identically zero',flush=True)
def main():
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('--emit',type=Path)
    args=ap.parse_args()
    quad_symbolic()
    A0,Pi=read_prefix(Path(__file__).with_name('prefix.json'))
    prefix(A0,Pi)
    x=verify_geometry()
    A,B,w=build(x,A0,Pi)
    print('seven positive scalar masses',[v.print()for v in w],flush=True)
    assert all(v.sign()==1 for v in w)
    for i,row in enumerate(A):
        assert all(Box(u).l==0 and Box(u).h==0 for u in row[i:]),i
    assert all(any(Box(u).h<Box(v).l or Box(v).h<Box(u).l for u,v in zip(A[i],A[j]))
               for i,j in combinations(range(14),2)), 'literal remaining rows are distinct'
    ph=rk(A)
    for n,expected in enumerate((1,1,2,4,9,20,48,115,286),1):
        ts=trees(n-1)
        assert len(ts)==expected
        vals=[fact(t)*sum(u*v for u,v in zip(ph(t),B))-1 for t in ts]
        for e in vals:e.char()
        top=max(max(abs(e.l),abs(e.h))for e in vals)
        print('size',n,'checked',len(ts),'interval absolute bound',float(F(top,S)),flush=True)
    t=()
    for _ in range(9):t=(t,)
    r=fact(t)*sum(u*v for u,v in zip(ph(t),B))-1
    assert r.h<0 and r.l>-4*S and r.h<(-3*S)
    print('strict failed tenth tall condition',r.print(),flush=True)
    print('Stage 14 is last and at clock 1; 3 literal merges into stages 1,8,9.',flush=True)
    if args.emit:
        fmt=lambda u:[str(Box(u).l),str(Box(u).h)]
        args.emit.write_text(json.dumps({'meaning':'closed integer-pair intervals divided by 2^bits; exact point specified in proof',
            'bits':BITS,'isolating_xi':[str(XL),str(XU)],'v_w_z_box':[[str(a),str(b)]for a,b in roots],
            'A':[[fmt(u)for u in row[:i]]for i,row in enumerate(A)],'b':[fmt(u)for u in B],
            'ten_tall_cleared_defect':fmt(r)},indent=2)+'\\n')
if __name__=='__main__':main()

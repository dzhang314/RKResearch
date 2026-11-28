#!/usr/bin/env python3
"""Independent stdlib replay of small quartic-mask residue algebras."""
from fractions import Fraction as Q
from math import comb
from functools import reduce

class FF:
    def __init__(self,p,g):
        self.p=p; self.g=tuple(g); self.n=len(g)-1; assert g[-1]==1
    def __call__(self,a):
        if isinstance(a,E):
            assert a.F is self
            return a
        if isinstance(a,Q):
            a=(a.numerator*pow(a.denominator,-1,self.p))%self.p
        if isinstance(a,int):
            a=[a]
        a=list(a)
        return E(tuple((a+[0]*self.n)[i]%self.p for i in range(self.n)),self)
class E:
    __slots__=('v','F')
    def __init__(self,v,F):self.v=v;self.F=F
    def __bool__(self):return any(self.v)
    def __eq__(self,o):
        try: k=self.F(o)
        except: return False
        return self.v==k.v
    def __add__(self,o):
        F=self.F;o=F(o)
        return F(tuple(a+b for a,b in zip(self.v,o.v)))
    def __neg__(self):return self.F(tuple(-a for a in self.v))
    def __sub__(self,o):return self+-self.F(o)
    def __rsub__(self,o):return self.F(o)+-self
    def __radd__(self,o):return self+o
    def __mul__(self,o):
        F=self.F;o=F(o);n=F.n;p=F.p
        a=[0]*(2*n-1)
        for i,u in enumerate(self.v):
            if u:
                for j,v in enumerate(o.v):
                    a[i+j]=(a[i+j]+u*v)%p
        for k in range(2*n-2,n-1,-1):
            if a[k]:
                for j in range(n):
                    a[k-n+j]=(a[k-n+j]-a[k]*F.g[j])%p
        return F(a)
    def __rmul__(self,o):return self*o
    def __pow__(self,k):
        if k<0:return self.inv()**(-k)
        out=self.F(1);b=self
        while k:
            if k&1:out=out*b
            k//=2
            if k:b=b*b
        return out
    def inv(self):
        assert self
        return self**(self.F.p**self.F.n-2)
    def __truediv__(self,o):return self*self.F(o).inv()
    def __rtruediv__(self,o):return self.F(o)*self.inv()
    def __repr__(self):return repr(self.v)

def ad(a,b):
    return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                  for i in range(max(len(a),len(b)))])
def trim(a):
    a=list(a)
    while a and not a[-1]:a.pop()
    return a
def scl(a,k):return trim([v*k for v in a])
def sub(a,b):return ad(a,scl(b,-1))
def mul(a,b):
    if not a or not b:return []
    c=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            c[i+j]+=u*v
    return trim(c)
def eva(a,t):
    r=0
    for c in reversed(a):r=r*t+c
    return r
def div(a,b):
    a=trim(a); b=trim(b)
    assert b
    out=[0]*max(0,(len(a)-len(b)+1))
    inv=b[-1].inv()
    while len(a)>=len(b):
        k=len(a)-len(b); f=a[-1]*inv;out[k]=f
        a=sub(a,[0]*k+scl(b,f))
    return trim(out),a
def exquo(a,b):
    q,r=div(a,b)
    assert not r, ('nonstructural remainder',r)
    return q
def gcd(a,b):
    while b:a,b=b,div(a,b)[1]
    return scl(a,a[-1].inv()) if a else []
def hull(F,ys):
    return reduce(mul,([F(-y),F(1)] for y in ys),[F(1)])
def integ(F,L):
    return [F(0)]+[v/F(i) for i,v in enumerate(L,1)]
def leg(F,n,a):
    return [F(k*(-1)**(n-k)*comb(n,k)*comb(n+k,k))*a**(k-1) for k in range(1,n+1)]
def modpow(a,n,g):
    q=[g[-1]]
    for bit in bin(n)[2:]:
        q=div(mul(q,q),g)[1]
        if bit=="1":
            q=div(mul(q,a),g)[1]
    return q

def irreducible(F,g):
    # A reducible polynomial of degree n has an irreducible factor
    # of some degree k<=n/2; that factor divides X^(p^k)-X.
    X=[F(0),F(1)]
    n=len(g)-1
    h=div(X,g)[1]
    for i in range(1,n+1):
        h=modpow(h,F.p,g)
        if i<=n//2:
            assert len(gcd(sub(h,X),g))==1
    assert not sub(h,div(X,g)[1])

def solve(F,M,rhs):
    N=len(M);M=[list(row)+[v] for row,v in zip(M,rhs)]
    for k in range(N):
        j=next((j for j in range(k,N) if M[j][k]),None)
        assert j is not None
        M[k],M[j]=M[j],M[k]
        inv=M[k][k].inv();M[k]=[c*inv for c in M[k]]
        for j in range(N):
            if j!=k:
                fac=M[j][k]
                M[j]=[b-fac*c for b,c in zip(M[j],M[k])]
    return [row[-1] for row in M]

import json, sys
from pathlib import Path

DATA=json.loads(Path(__file__).with_name("quartic-projection.json").read_text())
RESIDUES={
 ("nonroot",0):(17,[[1,14,2,8,5,6,1,2,4,4,4,11,2,1],
                    [1,11,4,16,16,7,13,12,15,14,4,12,13,1]]),
 ("firstroot",0):(17,[[6,15,13,12,1],[10,16,5,16,1]]),
 ("firstroot",1):(19,[[14,16,14,1,1],[2,16,17,7,1],
                     [16,10,15,15,3,12,0,4,1,8,9,14,11,17,0,6,17,0,11,4,8,16,7,0,1]]),
}
def eval2(F,A,X,rows):
    n=max(i for i,j,c in rows);m=max(j for i,j,c in rows)
    aa=[F(1)]*(n+1);xx=[F(1)]*(m+1)
    for i in range(n):aa[i+1]=aa[i]*A
    for j in range(m):xx[j+1]=xx[j]*X
    return sum((c*aa[i]*xx[j] for i,j,c in rows),F(0))

def quotient_equations(F,typ,aa,xx,yy):
    o=F(1);z=F(0)
    P=hull(F,[z,o,xx,yy]); XP=[z]+P
    JP=integ(F,P);JXP=integ(F,XP);I0=eva(JP,o);I1=eva(JXP,o)
    D=2*xx*yy-xx-3*yy**2+2*yy
    U=3*xx**2-2*xx*yy-2*xx+yy
    assert aa*xx*(xx-1)*(2*xx-1)*yy*(yy-1)*(yy-xx)*D
    Ls=[[z]+leg(F,j,aa) for j in (5,6,7)]
    M=[[eva(L,s) for L in Ls] for s in (o,xx,yy)]
    def mode(reads):
        return reduce(ad,(scl(L,c) for L,c in zip(Ls,solve(F,M,reads))),[])
    if typ=="nonroot":
        R=scl(Ls[1],1/eva(Ls[1],o));Rx=eva(R,xx)
        assert eva(JP,xx)==Rx*I0
        D1=eva(JXP,xx)-Rx*I1
        th=-yy**3*(yy-1)**3*U/(xx**3*(xx-1)**3*D)
        V=mode([z,o,th])
        A0=sub(JP,scl(R,I0))
        A1=sub(sub(JXP,scl(R,I1)),scl(V,D1))
    else:
        assert not eva(Ls[1],o) and not I0
        DB=5*xx**2-5*xx+1
        ex=-(7*xx**2-7*xx+2)/1260
        r1=xx**3*(15*xx**3-49*xx**2+55*xx-20)/DB
        k1=-30*xx**3*(xx-1)**3/DB
        k=scl(Ls[1],k1/eva(Ls[1],xx))
        K1=eva(integ(F,[z]+XP),o)-ex
        assert I1
        ry=(eva(JXP,yy)-eva(k,yy)*K1)/I1
        r=mode([o,r1,ry])
        A0=sub(JP,scl(k,I1))
        A1=sub(sub(JXP,scl(r,I1)),scl(k,K1))
    return exquo(A0,P),exquo(A1,P)

def bezout(f,g):
    r,s=f,g;b,c=[f[0].F(1)],[]
    d,e=[],[f[0].F(1)]
    while s:
        u,v=div(r,s);r,s=s,v
        b,c=c,sub(b,mul(c,u))
        d,e=e,sub(d,mul(e,u))
    assert len(r)==1
    return scl(b,1/r[0]),scl(d,1/r[0])

def replay():
    native=[]
    for (typ,j),(p,factors) in RESIDUES.items():
        assert all(p%d for d in range(2,1+int(p**.5)))
        ff=FF(p,[0,1]);src=DATA[typ]
        base=list(map(ff,src["factors"][j]))
        assert len(set(map(tuple,factors)))==len(factors)
        assert reduce(mul,(list(map(ff,f)) for f in factors),[ff(1)])==scl(base,1/base[-1])
        rec=[]
        for f in factors:
            irreducible(ff,list(map(ff,f)))
            F=FF(p,f);xx=F([0,1])
            lc=eval2(F,F(0),xx,src["linear"][0]);assert lc
            aa=-eval2(F,F(0),xx,src["linear"][1])/lc
            assert all(not eval2(F,aa,xx,g) for g in src["G"])
            yy=xx/(2*xx-1) if typ=="nonroot" else (5*xx-3)/(10*xx-5)
            t1,t2=quotient_equations(F,typ,aa,xx,yy)
            assert len(t1)==3 and len(t2)==4 and len(gcd(t1,t2))==1
            S,T=bezout(t1,t2)
            assert ad(mul(S,t1),mul(T,t2))==[F(1)]
            rec.append(F.n)
            dump=lambda a:[list(v.v) for v in a]
            native.append([p,f,dump(t1),dump(t2),dump(S),dump(T),
                           list(lc.v),list(lc.inv().v),list(t1[-1].inv().v)])
        print(f"{typ} x degree {len(base)-1}: p={p}, factors {rec}, lifted a and t pivots units; (2,3) roots disjoint")
    if len(sys.argv)>1:
        assert sys.argv[1]=="--native"
        Path(sys.argv[2]).write_text(json.dumps(native,separators=(",",":"))+"\n")
    return native

if __name__=="__main__":
    replay()

#!/usr/bin/env python3
"""Independent exact standard-library finite-algebra replay."""
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

def nonroot_y_poly(F,a,x):
    z=F(0);o=F(1)
    D=[-x,2*x+2,F(-3)]
    P=[-10*x*x,20*x*x+5*x,-18*x*x-6*x,6*x*x+8*x-3,2-4*x]
    G=ad(scl(mul(D,leg(F,6,a)),2*x-1),[z,z]+scl(P,eva(leg(F,6,o),a)))
    return exquo(G,hull(F,[o,x]))

def g1_y_poly(F,a,x):
    z=F(0);o=F(1)
    D=[-x,2*x+2,F(-3)]
    U=[3*x*x-2*x,1-2*x]
    G=ad(scl(mul(D,leg(F,6,a)),x*x*(x-1)**3),
          scl(mul(hull(F,[z,z,o,o,o]),U),eva(leg(F,6,a),x)))
    return exquo(G,hull(F,[o,x]))

def fourth(F,first,aa,xx,yy):
    z=F(0);o=F(1)
    xx=F(xx);aa=F(aa);yy=F(yy)
    P=hull(F,[z,o,xx,yy]);XP=[z]+P
    JP=integ(F,P);JXP=integ(F,XP);I0=eva(JP,o);I1=eva(JXP,o)
    D=2*xx*yy-xx-3*yy**2+2*yy;U=3*xx**2-2*xx*yy-2*xx+yy
    (aa*xx*(xx-1)*yy*(yy-1)*(yy-xx)*D).inv()
    Ls=[[z]+leg(F,j,aa) for j in (5,6,7)]
    E=[[eva(L,s) for L in Ls] for s in (o,xx,yy)]
    def mode(reads):
        from functools import reduce
        return reduce(ad,(scl(L,c) for L,c in zip(Ls,solve(F,E,reads))),[])
    if not first:
        (2*xx-1).inv()
        R=scl(Ls[1],1/eva(Ls[1],o));Rx=eva(R,xx)
        D0=eva(JP,xx)-Rx*I0;D1=eva(JXP,xx)-Rx*I1
        th=-yy**3*(yy-1)**3*U/(xx**3*(xx-1)**3*D)
        V=mode([z,o,th])
        A0=sub(sub(JP,scl(R,I0)),scl(V,D0))
        A1=sub(sub(JXP,scl(R,I1)),scl(V,D1))
    else:
        assert not eva(Ls[1],o)
        DB=5*xx**2-5*xx+1;ex=-(7*xx**2-7*xx+2)/1260
        r1=xx**3*(15*xx**3-49*xx**2+55*xx-20)/DB
        k1=-30*xx**3*(xx-1)**3/DB
        k=scl(Ls[1],k1/eva(Ls[1],xx))
        K1=eva(integ(F,[z]+XP),o)-ex
        ry,_=solve(F,[[I0,I1],[I1,K1]],[eva(JP,yy),eva(JXP,yy)])
        r=mode([o,r1,ry])
        A0=sub(sub(JP,scl(r,I0)),scl(k,I1))
        A1=sub(sub(JXP,scl(r,I1)),scl(k,K1))
    A=exquo(A0,P);B=exquo(A1,P)
    assert len(A)==4,('degree A',len(A)-1)
    return A,B

import json
from pathlib import Path

class Extension:
    def __init__(self,B,g):
        self.B=B;self.g=g;self.n=len(g)-1
        assert g[-1]==B(1)
    def __call__(self,a):
        if isinstance(a,Ext):
            assert a.F is self
            return a
        if not isinstance(a,list):a=[a]
        return Ext(self,div(list(map(self.B,a)),self.g)[1])

class Ext:
    def __init__(self,F,c):self.F=F;self.c=c
    def __bool__(self):return bool(self.c)
    def __eq__(self,o):return self.c==self.F(o).c
    def __add__(self,o):return Ext(self.F,ad(self.c,self.F(o).c))
    __radd__=__add__
    def __neg__(self):return Ext(self.F,scl(self.c,-1))
    def __sub__(self,o):return self+-self.F(o)
    def __rsub__(self,o):return self.F(o)+-self
    def __mul__(self,o):return self.F(mul(self.c,self.F(o).c))
    __rmul__=__mul__
    def __pow__(self,k):
        if k<0:return self.inv()**(-k)
        z=self.F(1);p=self
        while k:
            if k%2:z=z*p
            k//=2
            if k:p=p*p
        return z
    def inv(self):
        assert self
        B=self.F.B
        a,b=self.F.g,self.c;u,v=[],[B(1)]
        while b:
            j,r=div(a,b)
            a,b=b,r
            u,v=v,sub(u,mul(j,v))
        assert len(a)==1
        return self.F(scl(u,a[0].inv()))
    def __truediv__(self,o):return self*self.F(o).inv()
    def __rtruediv__(self,o):return self.F(o)*self.inv()

def irreducible_at(B,g):
    X=[B(0),B(1)];q=B.p**B.n
    n=len(g)-1
    v=div(X,g)[1]
    for i in range(1,n+1):
        v=modpow(v,q,g)
        if i<=n//2:assert len(gcd(sub(v,X),g))==1
    assert v==div(X,g)[1]

def main():
    path=Path(__file__).parent
    data=json.loads((path/'projections.json').read_text())
    rows=json.loads((path/'residues.json').read_text())
    for name,p,bs in rows:
        assert all(p%d for d in range(2,1+int(p**.5)))
        fp=FF(p,[0,1])
        out=list(map(fp,data['base'][name]))
        assert out[-1] and len(set(tuple(f) for f,parts in bs))==len(bs)
        assert reduce(mul,(list(map(fp,f)) for f,parts in bs),[fp(1)])==scl(out,1/out[-1])
        count=0;degree=0
        for f,parts in bs:
            irreducible(fp,list(map(fp,f)))
            B=FF(p,f);z=B([0,1]) if B.n>1 else B(-f[0]);o=B(1)
            if name=='c1':
                a=z;y=1/a
                den,num=[eva(list(map(B,v)),a) for v in data["linear"]]
                assert den
                x=-num/den
                A,C=fourth(B,False,a,x,y)
                assert len(gcd(A,C))==1
                count+=1;degree+=B.n
                continue
            if name=='c1root':
                a=z;y=1/a
                X=[eva(list(map(B,v)),a) for v in data["c2"]]
                assert len(X)==7 and X[-1]
                poly=exquo(X,[-o,o])
            else:
                a,x=(o,z) if name=='a1' else (z,1/z)
                poly=(g1_y_poly if name=='b1root' else nonroot_y_poly)(B,a,x)
            assert len(poly)==6 and poly[-1] and parts
            P=[list(map(B,g)) for g in parts]
            assert reduce(mul,P,[o])==scl(poly,1/poly[-1])
            for g in P:
                irreducible_at(B,g)
                F=Extension(B,g)
                q=F([0,1])
                x0,y0=(q,F(y)) if name=='c1root' else (F(x),q)
                A,C=fourth(F,name.endswith('root'),F(a),x0,y0)
                assert len(gcd(A,C))==1
                count+=1;degree+=B.n*F.n
        print(f"{name}: p={p}; {count} residue fields, total degree {degree}; unit cubic leading and no fourth root")

if __name__=="__main__":
    main()

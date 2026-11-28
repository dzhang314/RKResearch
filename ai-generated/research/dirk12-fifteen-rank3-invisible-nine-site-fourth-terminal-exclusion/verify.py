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

def div0(a,b,p):
    a=list(a);q=[0]*max(0,len(a)-len(b)+1)
    iv=pow(b[-1],-1,p)
    while len(a)>=len(b):
        i=len(a)-len(b);c=a[-1]*iv%p;q[i]=c
        for j,v in enumerate(b):a[i+j]=(a[i+j]-c*v)%p
        a=trim0(a)
    return trim0(q),a
def trim0(a):
    while a and not a[-1]:a.pop()
    return a
def mul0(a,b,p):
    if not a or not b:return []
    v=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):v[i+j]=(v[i+j]+x*y)%p
    return trim0(v)
def sub0(a,b,p):
    return trim0([((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%p
                  for i in range(max(len(a),len(b)))])
def gcd0(a,b,p):
    while b:a,b=b,div0(a,b,p)[1]
    return [(x*pow(a[-1],-1,p))%p for x in a] if a else []
def e_inv(self):
    p=self.F.p
    a,b=list(self.F.g),trim0(list(self.v))
    u,v=[],[1]
    while b:
        q,r=div0(a,b,p);a,b=b,r;u,v=v,sub0(u,mul0(q,v,p),p)
    assert len(a)==1
    iv=pow(a[0],-1,p)
    return self.F([iv*x%p for x in u])
E.inv=e_inv

def irreducible0(f,p):
    n=len(f)-1
    if n==1:return
    def pw(v,k):
        u=[1]
        for d in bin(k)[2:]:
            u=div0(mul0(u,u,p),f,p)[1]
            if d=='1':u=div0(mul0(u,v,p),f,p)[1]
        return u
    X=[0,1];q=X
    for i in range(1,n+1):
        q=pw(q,p)
        if i<=n//2:assert gcd0(sub0(q,X,p),f,p)==[1]
    assert q==X

def base(p,raw,factors):
    assert all(p%i for i in range(2,1+int(p**.5)))
    assert raw[-1]%p
    given=1;got=[1]
    for f in factors:
        assert f[-1]==1
        got=mul0(got,f,p)
        irreducible0(f,p)
    assert got==[(x*pow(raw[-1],-1,p))%p for x in raw]
    assert len(set(map(tuple,factors)))==len(factors)

def first(R):
    src=json.loads((R/'first-root-projection.json').read_text())
    for name in ('half','quartic'):
        p,rows=json.loads((R/('first-res-'+name+'.json')).read_text())
        base(p,[0,1] if name=='half' else [1,-18,84,-132,66],[f for f,gs in rows])
        n=0;deg=0
        for f,gs in rows:
            B=FF(p,f);a=B(Q(1,2)) if name=='half' else B([0,1])
            def list_coeff(group):
                return [eva([B(Q(*z)) for z in row],a) for row in src[name][group]]
            b,u,v=map(list_coeff,('base','lead','constant'))
            assert len(b)==21 and b[-1]
            gs=[list(map(B,g)) for g in gs]
            assert all(g[-1]==B(1) for g in gs)
            assert reduce(mul,gs,[B(1)])==scl(b,1/b[-1])
            assert len(set(tuple(z.v for z in g) for g in gs))==len(gs)
            for g in gs:
                irreducible_at(B,g)
                F=Extension(B,g);x=F([0,1]);aa=F(a);t=1/aa
                den=eva(list(map(F,u)),x);assert den
                y=-eva(list(map(F,v)),x)/den
                assert t*(t-1)*(t-x)*(t-y)
                A,C=fourth(F,True,aa,x,y)
                assert eva(A,t) or eva(C,t)
                n+=1;deg+=B.n*F.n
        print(f"first-root {name}: p={p}; {n} residue fields, total degree {deg}; fourth physical gate nonzero")

def gpoly(F,a,x,rows,var):
    aa=[F(1)]*(max(i for i,j,k,c in rows)+1)
    xx=[F(1)]*(max(j for i,j,k,c in rows)+1)
    for i in range(1,len(aa)):aa[i]=aa[i-1]*a
    if var!=1:
        for i in range(1,len(xx)):xx[i]=xx[i-1]*x
    v=[F(0)]*(max(row[var] for row in rows)+1)
    for row in rows:
        i,j,k,c=row
        v[row[var]]+=aa[i]*xx[j]*c
    return trim(v)

def nonroot(R):
    src=json.loads((R/'nonroot-projection.json').read_text())
    for j,(p,fs) in enumerate(json.loads((R/'nonroot-residues.json').read_text())):
        base(p,src['a'][j],fs)
        for f in fs:
            F=FF(p,f);a=F([0,1]) if F.n>1 else F(-f[0]);o=F(1);t=1/a
            assert a*(a-1)*eva(leg(F,6,o),a)
            G2=gpoly(F,a,o,src['G2'],1);H=gpoly(F,a,o,src['H'],1)
            assert len(G2)==6
            if j!=2:
                den,num=[eva(list(map(F,p)),a) for p in src["linear"]]
                x=o if j==0 else t if j==3 else (-num/den)
                assert len(gcd(exquo(G2,[-x,o]),H))==1
                if j==1:
                    G3=gpoly(F,a,x,src['G3'],2);GE=gpoly(F,a,x,src['GE'],2)
                    assert len(G3)==6
                    assert len(gcd(exquo(G3,[-t,o]),GE))==1
            else:
                g=gcd(G2,H);assert len(g)==2
                x=-g[0]
                G3=gpoly(F,a,x,src['G3'],2);GE=gpoly(F,a,x,src['GE'],2)
                assert len(G3)==6
                g=gcd(G3,GE);assert len(g)==2
                y=-g[0]
                assert t*(t-1)*(t-x)*(t-y)
                A,C=fourth(F,False,a,x,y)
                assert eva(A,t) or eva(C,t)
        print(f"nonroot degree {len(src['a'][j])-1}: p={p}; {[len(f)-1 for f in fs]}; "
              +("fourth physical gate nonzero" if j==2 else "exact characteristic-zero collision is sole fibre"))

def main():
    R=Path(__file__).parent
    first(R);nonroot(R)

if __name__=='__main__':
    main()

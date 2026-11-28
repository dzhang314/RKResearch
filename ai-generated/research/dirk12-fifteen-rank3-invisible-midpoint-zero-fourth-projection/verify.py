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

def instance(F,aa,x,y,t):
    o=F(1);z=F(0)
    (x*y*(x-1)*(y-1)*(y-x)*t*(t-1)*(t-x)*(t-y)).inv()
    D=2*x*y-x-3*y*y+2*y
    DB=5*x*x-5*x+1
    ep=-(7*x*x-7*x+2)/1260
    omega=y*(x-y)*(y-1)/(2*D)
    beta=x*(x-1)*(2*x-1)/(2*DB)
    rb=x**3*(15*x**3-49*x*x+55*x-20)/DB
    kb=-30*x**3*(x-1)**3/DB
    T0=hull(F,[z,o,x,y]); T1=[z]+T0
    P,K0=eva(integ(F,T0),o),eva(integ(F,T1),o)
    K1=eva(integ(F,[z]+T1),o)-ep
    ry,_=solve(F,[[P,K0],[K0,K1]],[eva(integ(F,T0),y),eva(integ(F,T1),y)])
    G=[[z]+leg(F,j,aa) for j in (5,6,7)]
    modes=[[eva(m,s) for m in G] for s in (o,x,y)]
    def fromm(rr):
        return reduce(ad,(scl(m,v) for m,v in zip(G,solve(F,modes,rr))),[])
    r=fromm([o,rb,ry])
    k=scl(G[1],kb/eva(G[1],x))
    def read(V):
        J=integ(F,V);JX=integ(F,[z]+V)
        return sub(sub(J,scl(r,eva(J,o))),
                   scl(k,eva(JX,o)-ep*(V[5] if len(V)>5 else z)))
    assert not eva(read(T0),t) and not eva(read(T1),t)
    W=hull(F,[z,z,o,o,F(Q(1,2))])
    Wx,Wy=eva(W,x),eva(W,y)
    L=scl(hull(F,[z,o]),1/(x*(x-1)))
    tau=eva(read(L),y)-omega*eva(L,y)
    LB=scl(hull(F,[z,o,y]),1/(x*(x-1)*(x-y)))
    LC=scl(hull(F,[z,o,x]),1/(y*(y-1)*(y-x)))
    B,C=eva(read(LB),t),eva(read(LC),t)
    Z=fromm([z,-beta*beta*Wx,(y-x-omega-beta)*tau*Wx-omega*omega*Wy])
    actual=(t-x-beta)*B*Wx+(t-y-omega)*C*Wy-C*tau*Wx
    if actual!=eva(Z,t):return 'commutator',None
    K=hull(F,[z,o,x,y,t]);K1=[z]+K
    J=integ(F,K1)
    A_K1=sub(J,fromm([eva(J,s) for s in (o,x,y)]))
    if eva(A_K1,t):return 'sixth input',None
    A_K=read(K)
    EE=exquo(sub(A_K1,[z]+A_K),K)
    assert len(EE)==4,('f leading',len(EE)-1)
    # n_j = integral Y^(j+1) Q(1-Y) where Q=(X-f)K and f is
    # now our ordinary physical coordinate, left as polynomial argument.
    from math import comb
    Kphys=hull(F,[z,aa,aa*x,aa*y,aa*t])
    Kref=[sum(c*(-1)**j*comb(i,j) for i,c in enumerate(Kphys) if j<=i)
          for j in range(len(Kphys))]
    nm=[[sum(v/(i+j+2)-v/(i+j+3) for i,v in enumerate(Kref)),
         -sum(v/(i+j+2) for i,v in enumerate(Kref))] for j in range(5)]
    N0,N1,N2,N3,N4=nm
    R1=sub(mul(sub(scl(mul(N1,N1),3),mul(N0,N2)),N3),
           scl(mul(N1,mul(N2,N2)),2))
    R2=sub(scl(mul(sub(scl(mul(N1,N1),9),scl(mul(N0,N2),4)),mul(N2,N4)),2),
           scl(mul(sub(scl(mul(N1,N1),3),mul(N0,N2)),mul(N3,N3)),5))
    Ef=[c/aa**i for i,c in enumerate(EE)]
    return 'fifth',gcd(gcd(Ef,R1),R2)

def coeff(R):
    d=max(i for i,j,k,c in R);v=[0]*(d+1)
    for i,j,k,c in R:
        assert j==k==0
        v[i]=c
    return v

def gpol(F,x,y,rows,var):
    a=[F(1)]*(max(i for i,j,k,c in rows)+1)
    b=[F(1)]*(max(j for i,j,k,c in rows)+1)
    for i in range(1,len(a)):a[i]=a[i-1]*x
    if var!=1:
        for i in range(1,len(b)):b[i]=b[i-1]*y
    v=[F(0)]*(max(row[var] for row in rows)+1)
    for row in rows:
        i,j,k,c=row;v[row[var]]+=a[i]*b[j]*c
    return trim(v)

def main():
    R=Path(__file__).parent
    s=json.loads((R/'projection.json').read_text())
    d=json.loads((R/'residues.json').read_text())
    p=d['p']
    assert p==17
    base(p,coeff(s['bases'][1]),[f for f,gs in d['f20']])
    dims=[]
    for f,gs in d['f20']:
        B=FF(p,f);x=B([0,1]);o=B(1)
        Y=gpol(B,x,o,s['G3'],1);H=gpol(B,x,o,s['H'],1)
        assert len(Y)==6
        gy=gcd(Y,H);assert len(gy)==2;y=-gy[0]
        L=gpol(B,x,y,s['E2'],2);H=gpol(B,x,y,s['E3'],2)
        assert len(L)==3 or len(H)==4
        T=gcd(L,H);assert len(T)==3
        ts=[list(map(B,cs)) for cs in gs]
        assert reduce(mul,ts,[o])==T
        assert len(set(tuple(z.v for z in g) for g in ts))==len(ts)
        for g in ts:
            irreducible_at(B,g)
            E=Extension(B,g);t=E([0,1])
            how,_=instance(E,E(Q(1,2)),E(x),E(y),t)
            assert how=='commutator'
            dims.append(B.n*E.n)
    N=coeff(s['bases'][0]);p=137;lc=N[-1]%p
    assert lc
    reduced=[v*pow(lc,-1,p)%p for v in N]
    base(p,N,[reduced])
    assert sum(dims)==40
    print(f"degree20 excluded by literal fourth commutator in residues {dims}; degree36 irreducible modulo 137")

if __name__=='__main__':
    main()

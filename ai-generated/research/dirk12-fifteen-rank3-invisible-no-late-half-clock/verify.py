#!/usr/bin/env python3
"""Independent degree-25 exact residue replay, ordinary no-late half-clock.

Finite arithmetic helpers adapted from the separately reviewed late-zero checker.
Only the Python standard library is used; factors are verified, not guessed.
"""
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

def y_equation(F,a):
    x=F(Q(1,2))
    L=leg(F,6,a)
    D=[F(1),F(-6),F(6)]
    rhs=scl(hull(F,[F(0),F(0),F(1),F(1),F(1)]),16*eva(L,x))
    V=sub(mul(D,L),rhs)
    Y=exquo(V,hull(F,[F(1),x]))
    assert len(Y)==6 and Y[-1]
    return scl(Y,Y[-1].inv())

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

def check(F,a,y):
    a=F(a);x=F(Q(1,2));y=F(y);one=F(1)
    D=6*y*y-6*y+1
    assert a*y*(y-1)*(y-x)*D
    w=y*(y-1)*(2*y-1)/(2*D)
    rc=-y**3*(24*y**4-114*y**3+204*y**2-165*y+50)/D
    rb=F(Q(23,16));kb=F(Q(-15,8));eps=F(Q(-1,5040))
    Ls=[[F(0)]+leg(F,j,a) for j in (5,6,7)]
    k_poly=scl(Ls[1],kb/eva(Ls[1],x))
    M=[[eva(L,s) for L in Ls] for s in (one,x,y)]
    def modes(y1,y2,y3):
        coeff=solve(F,M,[y1,y2,y3])
        return reduce(ad,(scl(L,c) for L,c in zip(Ls,coeff)),[])
    r=modes(one,rb,rc)
    W=hull(F,[F(0),F(0),one,one,x])
    Z=modes(F(0),F(0),-w*w*eva(W,y))
    V0=hull(F,[F(0),one,x,y])
    def A(p):
        J=integ(F,p);I=eva(J,one)
        I2=eva(integ(F,[F(0)]+list(p)),one)
        return sub(sub(J,scl(r,I)),scl(k_poly,I2-(eps*p[5] if len(p)==6 else 0)))
    d=exquo(A(V0),V0);E5=sub(exquo(A([F(0)]+V0),V0),[0]+d)
    V=A(W)
    Q0=[-y-w,F(1)]
    E7=exquo(sub(sub(mul(Q0,V),mul(d,ad(V,mul(Q0,W)))),Z),V0)
    return len(E5)-1,len(E7)-1,len(gcd(E5,E7))-1


P=43
ROOTS=(2,9,22,35,42)
FACTORS={
    2: [[8,1],[10,1],[27,38,35,1]],
    9: [[32,35,11,5,5,1]],
    22: [[19,1],[19,15,1],[13,26,1]],
    35: [[4,1],[3,8,27,21,1]],
    42: [[5,21,1],[22,15,25,1]],
}


def main():
    assert 6**2<P<7**2 and all(P%d for d in range(2,7))
    F0=FF(P,[0,1])
    L=leg(F0,6,F0(1))
    assert L[-1] and L==scl(hull(F0,[F0(a) for a in ROOTS]),L[-1])
    n=deg=0
    for a in ROOTS:
        assert a and eva(L,F0(Q(a,2)))
        Y=y_equation(F0,F0(a))
        factors=[[F0(c) for c in f] for f in FACTORS[a]]
        assert len(set(tuple(f) for f in FACTORS[a]))==len(factors)
        assert reduce(mul,factors,[F0(1)])==Y
        for f in factors:
            irreducible(F0,f)
        print(f"ordinary a residue {a}: y factor degrees {[len(f)-1 for f in factors]}")
        for f in FACTORS[a]:
            F=FF(P,f);y=F(-f[0]) if F.n==1 else F([0,1])
            assert check(F,a,y)==(4,5,0),(a,f)
            n+=1;deg+=F.n
        print("  unit clock and mode guards; degree-4/5 equations coprime in every residue field")
    assert (n,deg)==(11,25)
    print(f"verified {n} irreducible factors, residue degree {deg}, prime {P}")


if __name__=="__main__":
    main()

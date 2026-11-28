#!/usr/bin/env python3
"""Exact bounded reduction for the late-zero fourth-live-row exclusion.

No approximate roots or factorization packages. The y factors are printed
certificates, with exact product and irreducibility independently checked.
All polynomials are represented in increasing coefficient order.
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
def mom(F,L):
    assert not L[0]
    return sum(v/F(k)*8 for k,v in enumerate(L[1:],1))-L[1]/2
def leg(F,n,a):
    return [F(k*(-1)**(n-k)*comb(n,k)*comb(n+k,k))*a**(k-1) for k in range(1,n+1)]
def det2(a,b,c,d):return a*d-b*c

P0=271
AF=[-2015,27800,-136800,312000,-330000,129888]
A_ROOTS=(11,82,99,134,191)
Y_FACTORS={
    11: [[119,1],[21,1,146,99,1]],
    82: [[122,1],[59,150,1],[56,215,1]],
    99: [[54,207,169,15,13,1]],
    134: [[206,1],[23,170,55,60,1]],
    191: [[71,1],[110,1],[6,177,267,1]],
}

def y_equation(F,a):
    x=F(Q(2,5))
    D=[-x,2*x+2,F(-3)]
    P=[-10*x*x,20*x*x+5*x,-18*x*x-6*x,6*x*x+8*x-3,2-4*x]
    L6=leg(F,6,a)
    H=ad(scl(mul(D,L6),2*x-1),
         scl([F(0),F(0)]+P,eva(L6,F(1))))
    assert len(H)==8
    Y=exquo(H,hull(F,[F(1),x]))
    return scl(Y,Y[-1].inv())

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

def check_branch(F,a,y):
    a=F(a);x=F(Q(2,5));y=F(y);one=F(1)
    D=2*x*y-x-3*y*y+2*y
    if not a*y*(y-1)*(y-x)*D: return ('guard clock/D',None)
    omega=y*(x-y)*(y-1)/(2*D)
    theta_y=-y**3*(y-1)**3*(3*x*x-2*x*y-2*x+y)/(x**3*(x-1)**3*D)
    L5,L6,L7=[leg(F,j,a) for j in (5,6,7)]
    L6a=eva(L6,one)
    if not L6a:return ('guard L6a',None)
    R=scl(L6,1/L6a)
    G5=[F(0)]+sub(L5,scl(R,eva(L5,one)))
    G7=[F(0)]+sub(L7,scl(R,eva(L7,one)))
    G5x,G7x,G5y,G7y=eva(G5,x),eva(G7,x),eva(G5,y),eva(G7,y)
    dd=det2(G5x,G7x,G5y,G7y)
    if not dd:return ('guard mode pivot',None)
    def combine(px,py):
        a=(px*G7y-G7x*py)/dd
        b=(G5x*py-px*G5y)/dd
        return ad(scl(G5,a),scl(G7,b))
    base=F(Q(54,625))*x
    B=combine(base,base*theta_y)
    W=hull(F,[F(0),F(0),one,one,x])
    P7=combine(F(0),-omega*omega*eva(W,y))
    Rlive=[F(0)]+R
    def go(L):
        JL=integ(F,L)
        return sub(sub(JL,scl(Rlive,eva(JL,one))),scl(B,mom(F,L)))
    D0=hull(F,[F(0),one,x,y])
    Dpoly=exquo(go(D0),D0)
    Eq5=sub(exquo(go([F(0)]+D0),D0),[F(0)]+Dpoly)
    assert mom(F,W)==0
    AA=go(W)
    q=[-y-omega,F(1)]
    Eq7=exquo(sub(sub(mul(q,AA),mul(Dpoly,ad(AA,mul(q,W)))),P7),D0)
    if Eq5 and Eq7:
        res=gcd(Eq5,Eq7)
        return ('ok', dict(gcd=len(res)-1,e5=len(Eq5)-1,e7=len(Eq7)-1))
    return ('zero reduced eq',None)

def main():
    p=P0
    assert p>0 and all(p%d for d in range(2,17)) and 16*16<=p<17*17
    F0=FF(p,[0,1])
    A=[F0(k) for k in AF]
    assert A[-1]
    assert A==scl(hull(F0,[F0(a) for a in A_ROOTS]),A[-1])
    degrees=0; components=0
    for a in A_ROOTS:
        a0=F0(a)
        assert a0 and eva(leg(F0,6,a0),F0(1))
        Y=y_equation(F0,a0)
        fac=[[F0(z) for z in h] for h in Y_FACTORS[a]]
        assert reduce(mul,fac,[F0(1)])==Y
        assert all(g!=h for i,g in enumerate(fac) for j,h in enumerate(fac) if i!=j)
        for h in fac: irreducible(F0,h)
        print(f"ordinary a residue {a}: y factor degrees {[len(g)-1 for g in fac]}")
        for g in Y_FACTORS[a]:
            F=FF(p,g)
            y=F(-g[0]) if F.n==1 else F([0,1])
            status,result=check_branch(F,a,y)
            assert status=='ok' and result==dict(gcd=0,e5=4,e7=5),(a,g,status,result)
            components+=1; degrees+=F.n
        print("  unit clocks and mode determinant; degree-4/5 equations coprime in all factors")
    assert components==11 and degrees==25
    print(f"verified all {components} irreducible factors, total residue degree {degrees}, prime {p}")

if __name__=="__main__":
    main()

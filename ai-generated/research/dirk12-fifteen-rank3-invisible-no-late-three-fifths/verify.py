#!/usr/bin/env python3
"""Standard-library exact residue replay for the no-late b/a=3/5 exclusion."""
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

AF=[-2015,52800,-361800,972000,-1113750,456192]
def y_equation(F,a):
    x=F(Q(3,5))
    D=[-x,2*x+2,F(-3)]
    P=[-10*x*x,20*x*x+5*x,-18*x*x-6*x,6*x*x+8*x-3,2-4*x]
    L6=leg(F,6,a)
    H=ad(scl(mul(D,L6),2*x-1),scl([F(0),F(0)]+P,eva(L6,F(1))))
    Y=exquo(H,hull(F,[F(1),x]))
    assert len(Y)==6 and Y[-1]
    return scl(Y,Y[-1].inv())

def check(F,a,y):
    a=F(a);x=F(Q(3,5));y=F(y);one=F(1)
    D=2*x*y-x-3*y*y+2*y
    assert a*y*(y-1)*(y-x)*D
    omega=y*(x-y)*(y-1)/(2*D)
    eps=F(Q(301847,3244350))
    moments=list(map(F,[Q(16437785,19092),Q(5920915,9546),Q(2998905,6364),Q(585585,1591),Q(1860859,6364),Q(14115683582,60020475)]))
    def M(p):
        assert not p[0] and len(p)<=7
        return sum(c*m for c,m in zip(p[1:],moments))
    ca=F(Q(43,23660));ka=-ca
    Ls=[[F(0)]+leg(F,j,a) for j in (5,6,7)]
    k_poly=scl(Ls[1],ka/eva(Ls[1],one))
    Q3=hull(F,[F(0),one,x])
    J3=integ(F,Q3)
    JN=M(Q3);JT=M([F(0)]+Q3)
    assert JN and ka and moments[0]*moments[2]-moments[1]**2
    def rr(s,beta):
        return (eva(J3,s)-beta*eva(Q3,s)-eva(k_poly,s)*JT)/JN
    rb,rc=rr(x,F(0)),rr(y,omega)
    modesM=[[eva(L,s) for L in Ls] for s in (one,x,y)]
    def modes(y1,y2,y3):
        coeff=solve(F,modesM,[y1,y2,y3])
        return reduce(ad,(scl(L,c) for L,c in zip(Ls,coeff)),[])
    r=modes(ca,rb,rc)
    W=hull(F,[F(0),F(0),one,one,x])
    Z=modes(F(0),F(0),-omega*omega*eva(W,y))
    V0=hull(F,[F(0),one,x,y])
    def A(p):
        J=integ(F,p)
        return sub(sub(J,scl(r,M(p))),scl(k_poly,M([F(0)]+p)-(eps*p[5] if len(p)==6 else 0)))
    d=exquo(A(V0),V0);E5=sub(exquo(A([F(0)]+V0),V0),[0]+d)
    V=A(W)
    Q0=[-y-omega,F(1)]
    E7=exquo(sub(sub(mul(Q0,V),mul(d,ad(V,mul(Q0,W)))),Z),V0)
    return len(E5)-1,len(E7)-1,len(gcd(E5,E7))-1


P=1399
ROOTS=(249,508,893,978,1096)
FACTORS={
    249: [[549,1],[915,583,1],[1219,1291,1]],
    508: [[399,1],[563,1],[727,988,1291,1]],
    893: [[892,1037,1],[1305,1158,566,1]],
    978: [[347,619,1],[1062,433,326,1]],
    1096: [[487,1],[584,1339,46,491,1]],
}


def main():
    assert 37**2<P<38**2 and all(P%d for d in range(2,38))
    R=FF(P,[0,1]); A=list(map(R,AF)); L=leg(R,6,R(1))
    assert A[-1] and A==scl(hull(R,list(map(R,ROOTS))),A[-1])
    n=deg=0
    for a in ROOTS:
        assert a and eva(L,R(a))
        ys=y_equation(R,R(a))
        fs=[list(map(R,f)) for f in FACTORS[a]]
        assert len(set(tuple(f) for f in FACTORS[a]))==len(fs)
        assert reduce(mul,fs,[R(1)])==ys
        for f in fs: irreducible(R,f)
        print(f"ordinary a residue {a}: y factor degrees {[len(f)-1 for f in fs]}")
        for f in FACTORS[a]:
            F=FF(P,f); y=F(-f[0]) if F.n==1 else F([0,1])
            assert check(F,a,y)==(4,5,0),(a,f)
            n+=1; deg+=F.n
        print("  unit guards, degree-4/5 equations coprime on every residue field")
    assert (n,deg)==(12,25)
    print(f"verified {n} irreducible factors, total residue degree {deg}, prime {P}")


if __name__=='__main__':
    main()

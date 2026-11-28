#!/usr/bin/env python3
"""Standalone exact prime-113 tower and determinant check, no external CAS."""
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

LD=[-42,840,-5040,12600,-13860,5544]

def elim(F,M, rhs, is_det=False):
    A=[list(row)+[v] for row,v in zip(M,rhs)]
    dt=F(1)
    for i in range(len(A)):
        j=next((j for j in range(i,len(A)) if A[j][i]),None)
        if j is None:
            if is_det:return F(0)
            raise AssertionError('singular pivot')
        if i!=j: A[i],A[j]=A[j],A[i]; dt=-dt
        k=A[i][i]
        dt*=k
        A[i]=[x/k for x in A[i]]
        for j,row in enumerate(A):
            if j!=i:
                k=row[i]
                A[j]=[u-k*v for u,v in zip(row,A[i])]
    return dt if is_det else [A[i][-1] for i in range(len(A))]

def h_poly(F,a):
    u=[F(Q(1,i+4))-(2-a)*F(Q(1,i+3))+(1-a)*F(Q(1,i+2)) for i in range(8)]
    M=[[u[i+j] for j in range(3)] for i in [1,2,3]]
    cc=elim(F,M,[-u[i+3] for i in [1,2,3]])
    powers=list(zip(*[elim(F,M,[F(k) if j==i else F(0) for j in range(3)])
                     for i,k in enumerate([1,Q(2,3),Q(1,4)])]))
    n0=u[3]+sum(c*t for c,t in zip(cc,u[:3]))
    n4=u[7]+sum(c*t for c,t in zip(cc,u[4:7]))
    b0=[F(Q(31,12))]+[sum(u[j]*powers[j][i] for j in range(3)) for i in range(3)]
    b4=[sum(u[4+j]*powers[j][i] for j in range(3)) for i in range(3)]+[F(Q(-1,13))]
    hh=sub(scl(b0,n4),[F(0)]+scl(b4,n0))
    assert len(hh)==5 and n0
    return scl(hh,1/hh[-1]), (cc,powers,n0,b0)

def cubic(F,h,const):
    cc, powers,n0,b0=const
    b0=list(map(F,b0))
    assert h and eva(b0,h)
    lam=-h*F(n0)/eva(b0,h)
    return [F(c)+lam*eva(list(map(F,p)),h) for c,p in zip(cc,powers)]+[F(1)]


class Alg:
    def __init__(self,B,c):
        self.B=B;self.coeff=[B(u) for u in c];self.n=len(c)-1
        assert self.coeff[-1]==B(1)
    def __call__(self,v):
        if isinstance(v,X) and v.A is self:return v
        if not isinstance(v,list):v=[self.B(v)]
        return X([self.B(c) for c in v]+[self.B(0)]*(self.n-len(v)),self)
class X:
    def __init__(self,v,A):self.v=v;self.A=A
    def __bool__(self):return any(self.v)
    def __eq__(self,v):return self.v==self.A(v).v
    def __neg__(self):return self.A([-v for v in self.v])
    def __add__(self,v):
        A=self.A;v=A(v)
        return A([a+b for a,b in zip(self.v,v.v)])
    __radd__=__add__
    def __sub__(self,v): return self+-self.A(v)
    def __rsub__(self,v):return self.A(v)+-self
    def __mul__(self,v):
        A=self.A;v=A(v)
        vals=[A.B(0)]*(2*A.n-1)
        for i,l in enumerate(self.v):
            for j,r in enumerate(v.v):
                vals[i+j]+=l*r
        for i in range(2*A.n-2,A.n-1,-1):
            for j in range(A.n):
                vals[i-A.n+j]-=vals[i]*A.coeff[j]
        return A(vals[:A.n])
    __rmul__=__mul__
    def __pow__(self,n):
        out=self.A(1)
        for _ in range(n):out*=self
        return out


def derivative_norm(F,C):
    B=Alg(F,C); b=B([F(0),F(1)])
    v=3*b*b+b*(2*C[2])+C[1]
    mat=list(zip(*[(v*b**i).v for i in range(3)]))
    return elim(F,mat,[F(0)]*3,True)


def gate_norm(F,a,C):
    B=Alg(F,C); b=B([F(0),F(1)])
    T=Alg(B,[B(C[1])+b*C[2]+b*b,b+C[2],B(1)]); c=T([B(0),B(1)])
    x=(1-T(b))*F(1/a); y=(1-c)*F(1/a)
    D=2*x*y-x-3*y*y+2*y
    S=3*x*x-2*x*y-2*x+y
    def L(s):
        u=T(0)
        for l in LD[::-1]: u=u*s+l
        return u
    G=x*x*(x-1)**3*D*L(y*a)+y*y*(y-1)**3*S*L(x*a)
    mat=list(zip(*[[k for z in (T(b**i)*c**j*G).v for k in z.v]
                   for j in range(2) for i in range(3)]))
    return elim(F,mat,[F(0)]*6,True)



P=113
ROOTS=(7,21,57,93,107)
FACTORS={
    7: [[43,1],[65,1],[40,48,1]],
    21: [[92,20,64,54,1]],
    57: [[84,1],[10,66,79,1]],
    93: [[51,1],[103,1],[62,5,1]],
    107: [[60,67,53,57,1]],
}
DETS={
    7: [((11,), (85,)), ((85,), (8,)), ((17,107),(0,109))],
    21: [((87,43,14,45),(27,87,108,68))],
    57: [((56,),(51,)),((103,70,90),(62,71,68))],
    93: [((9,),(82,)),((52,),(83,)),((95,109),(0,70))],
    107: [((31,86,7,90),(55,28,78,15))],
}


def main():
    assert 10**2<P<11**2 and all(P%j for j in range(2,11))
    R=FF(P,[0,1]); L=list(map(R,LD))
    assert L[-1] and L==scl(hull(R,list(map(R,ROOTS))),L[-1])
    n=degs=0
    for a in ROOTS:
        assert a
        H,co=h_poly(R,R(a))
        factors=[list(map(R,f)) for f in FACTORS[a]]
        assert len(set(tuple(f) for f in FACTORS[a]))==len(factors)
        assert reduce(mul,factors,[R(1)])==H
        for f in factors: irreducible(R,f)
        norms=[]
        for f in FACTORS[a]:
            F=FF(P,f); h=F(-f[0]) if F.n==1 else F([0,1])
            cc,ps,n0,b0=co
            cv=lambda v:v.v[0]
            C=cubic(F,h,([cv(v) for v in cc],[[cv(v) for v in row] for row in ps],
                         cv(n0),[cv(v) for v in b0]))
            dd=derivative_norm(F,C); gg=gate_norm(F,F(a),C)
            assert dd and gg
            norms.append((dd.v,gg.v))
            n+=1;degs+=F.n
        assert norms==DETS[a]
        print(f"a={a}, h factor degrees {[len(f)-1 for f in factors]}, derivative/third-gate units {norms}")
    assert (n,degs)==(10,20)
    print("exactly 10 irreducible h fields (20 degrees), all 120 ordered-pair residue degrees eliminated")


if __name__=='__main__':
    main()

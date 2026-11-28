#!/usr/bin/env python3
"""Exact standalone residue audit of the nonroot reflected-zero exclusion."""
from pathlib import Path
from itertools import combinations
import json
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


Qr=Q
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


def trim0(v):
    while v and not v[-1]:v.pop()
    return v
def div0(v,w,p):
    v=list(v);q=[0]*max(0,(len(v)-len(w)+1));iw=pow(w[-1],-1,p)
    while len(v)>=len(w):
        i=len(v)-len(w); d=v[-1]*iw%p;q[i]=d
        for j,b in enumerate(w):v[i+j]=(v[i+j]-d*b)%p
        trim0(v)
    return trim0(q),v
def sub0(v,w,p):
    return trim0([((v[i] if i<len(v) else 0)-(w[i] if i<len(w) else 0))%p
                  for i in range(max(len(v),len(w)))])
def mul0(v,w,p):
    if not v or not w:return []
    a=[0]*(len(v)+len(w)-1)
    for i,x in enumerate(v):
        for j,y in enumerate(w):a[i+j]=(a[i+j]+x*y)%p
    return trim0(a)
def inv(self):
    p=self.F.p
    a,b=list(self.F.g),trim0(list(self.v))
    v,w=[],[1]
    while b:
        q,r=div0(a,b,p)
        a,b=b,r
        v,w=w,sub0(v,mul0(q,w,p),p)
    assert len(a)==1
    iw=pow(a[0],-1,p)
    return self.F([x*iw%p for x in v])
E.inv=inv

def nm(F,a,rows):
    ap=[F(1)]
    for _ in range(max(k for k,j,c in rows)):ap.append(ap[-1]*a)
    hp=[F(0) for _ in range(max(j for k,j,c in rows)+1)]
    for k,j,c in rows:hp[j]+=F(c)*ap[k]
    return hp

def polypow(F,p,n):
 v=[F(1)]
 for _ in range(n): v=mul(v,p)
 return v
def comp(F,p,q):
 v=[]
 for c in reversed(p):v=ad(mul(v,q),[F(c)]) if v else [F(c)]
 return v

def first2(F,a):
 B=[F(1),F(-1)]
 L=list(map(F,LD)); L0=eva(L,a)
 raw=sub(scl(mul(sub(scl(B,2),[a]),comp(F,L,B)),a**4),
          scl(mul(polypow(F,B,3),ad(scl(polypow(F,B,2),2),ad(scl(B,-6*a),[5*a*a]))),L0))
 return exquo(raw,hull(F,[1-a]))
def third(F,a,B):
 x=(1-B)/a
 Y=[1/a,-1/a]
 D=ad([-x],ad(scl(Y,2*x+2),scl(polypow(F,Y,2),-3)))
 P=[-10*x*x,20*x*x+5*x,-18*x*x-6*x,6*x*x+8*x-3,2-4*x]
 L=list(map(F,LD))
 return ad(scl(mul(D,comp(F,L,[F(1),F(-1)])),2*x-1),
           scl(mul(polypow(F,Y,2),comp(F,P,Y)),eva(L,a)))

A3=[-2,21,-56,42]
A4=[1,-14,56,-84,42]

def Lin(F,a,h):
    I=[F(Qr(1,i+4))-(2-a)*F(Qr(1,i+3))+(1-a)*F(Qr(1,i+2)) for i in range(8)]
    mat=[[h*I[0],h*I[1],h*I[2],F(Qr(31,12))]]
    vs=[-h*I[3]]
    targets=[F(1),h*F(Qr(2,3)),h*h/4,h**3/13]
    for i in range(1,5):
        mat.append(I[i:i+3]+[-targets[i-1]])
        vs.append(-I[i+3])
    for idx in combinations(range(5),4):
        rows=[mat[i] for i in idx]; rhs=[vs[i] for i in idx]
        if not elim(F,rows,rhs,True):continue
        ans=elim(F,rows,rhs)
        if any(sum(a*b for a,b in zip(rr,ans))!=v for rr,v in zip(mat,vs)):
            return idx,None
        return idx,ans[:3]+[F(1)]
    raise AssertionError('loss of rank of complete moment system')


DATA=json.loads((Path(__file__).resolve().parent/'first-gate-norm.json').read_text())
FACT37=[
 [1,1],
 [13,1],
 [19,22,22,32,24,34,22,4,27,1],
 [29,34,29,31,1,36,34,12,9,28,1,13,11,21,24,23,19,7,26,4,1],
 [33,15,23,21,30,12,35,16,1,0,9,23,27,25,3,4,19,26,31,10,31,28,13,26,13,18,31,27,8,23,10,6,25,29,36,31,8,11,18,28,23,27,12,19,14,33,18,11,30,1],
 [19,12,7,30,7,34,8,9,17,5,4,16,7,18,34,14,11,15,3,22,24,3,23,35,28,9,6,2,7,23,3,12,22,15,11,15,10,26,36,36,18,28,31,7,2,25,5,19,2,29,7,15,1],
]
SING={
 (3,73):{18:[[10,1],[36,15,36,1]],
         40:[[33,1],[34,1],[62,52,1]],
         65:[[56,1],[67,1],[25,69,1]]},
 (4,37):{6:[[6,22,6,1]],
         8:[[18,1],[2,32,1]],
         30:[[11,1],[19,5,1]],
         32:[[5,1],[36,18,1]]},
}

def factor_audit(R,p,facs):
    assert p[-1]
    fp=[list(map(R,f)) for f in facs]
    assert len(set(tuple(f) for f in facs))==len(fp)
    assert scl(reduce(mul,fp,[R(1)]),p[-1])==p
    for g in fp:irreducible(R,g)

def regular():
    p=37; R=FF(p,[0,1])
    F0=list(map(R,DATA['Q']))
    assert len(F0)==133 and F0[-1]
    factor_audit(R,F0,FACT37)
    for f in FACT37:
        F=FF(p,f);a=F(-f[0]) if F.n==1 else F([0,1])
        assert a and eva(list(map(F,LD)),a)
        H,co=h_poly(F,a)
        HH=nm(F,a,DATA['H'])
        assert HH[-1] and H==scl(HH,HH[-1].inv())
        g=gcd(H,nm(F,a,DATA['p']))
        if len(g)==1:
            print(f"ordinary a residue degree {F.n}: no h"); continue
        assert len(g)==2
        h=-g[0]
        C=cubic(F,h,co)
        Bp=gcd(C,first2(F,a))
        if len(Bp)==1:
            print(f"ordinary a residue degree {F.n}: no second clock"); continue
        assert len(Bp)==2
        B=-Bp[0]
        CQ=exquo(C,hull(F,[B]))
        assert len(CQ)==3 and len(gcd(CQ,third(F,a,B)))==1
        print(f"ordinary a residue degree {F.n}: unique h and second lift; no true third clock")
    print("generic nonroot part: exact good reduction in all 132 ordinary clock residue degrees")

def exceptional():
    for (deg,p),tab in SING.items():
        R=FF(p,[0,1]); A=A3 if deg==3 else A4
        pa=list(map(R,A))
        assert pa[-1] and scl(hull(R,list(map(R,tab))),pa[-1])==pa
        total=count=0
        for a,ff in tab.items():
            assert a
            H=nm(R,R(a),DATA['H'])
            if deg==4:
                assert not H[-1]
                H=H[:-1]
            assert H[-1] and len(H)==(5 if deg==3 else 4)
            factor_audit(R,H,ff)
            for f in ff:
                F=FF(p,f); h=F(-f[0]) if F.n==1 else F([0,1])
                idx,C=Lin(F,F(a),h)
                assert idx==((0,1,2,3) if deg==3 else (0,1,2,4))
                assert C is not None and len(gcd(C,first2(F,F(a))))==1
                total+=F.n
                count+=1
            print(f"singular a degree {deg}, prime {p}, a={a}: h degrees {[len(f)-1 for f in ff]}, no second clock")
        assert (total,count)==((12,8) if deg==3 else (12,7))
        print(f"singular degree {deg}: {count} h fields of total residue degree {total}")

def main():
    assert 6**2<37<7**2 and all(37%j for j in range(2,7))
    assert 8**2<73<9**2 and all(73%j for j in range(2,9))
    regular();exceptional()


if __name__=='__main__':
    main()

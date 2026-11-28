"""Exact standalone half-half edge-dormant singular-contact fiber checks.

SymPy-only arithmetic; all coefficient systems are constructed directly.
"""
from functools import reduce
import sympy as s
import sympy as sym
from sympy import ZZ
from sympy.polys import galoistools as gt

TT=[1,-32,216,-480,330]
UU=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],
    [-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
INV=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],
     [-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]

def sumi(K,*args):return reduce(K.add,args,K.o)
def prodi(K,*args):return reduce(K.mul,args,K.i)
def powi(K,x,n):return prodi(K,*[x]*n)
def pol(K,cs,x):return reduce(lambda v,c:K.add(K.c(c),K.mul(x,v)),reversed(cs),K.o)

class OverZ:
    def __init__(self,R):
        self.R=R;self.o=R.zero;self.i=R.one
    def c(self,n): return self.R(n)
    @staticmethod
    def add(x,y): return x+y
    @staticmethod
    def sub(x,y): return x-y
    @staticmethod
    def mul(x,y): return x*y
    @staticmethod
    def neg(x): return -x

class Mod:
    def __init__(self,g,p):
        self.g=g;self.p=p;self.o=[];self.i=[1]
    def c(self,n):return [n%self.p] if n%self.p else []
    def add(self,x,y):return gt.gf_add(x,y,self.p,ZZ)
    def sub(self,x,y):return gt.gf_sub(x,y,self.p,ZZ)
    def neg(self,x):return gt.gf_neg(x,self.p,ZZ)
    def mul(self,x,y):return gt.gf_rem(gt.gf_mul(x,y,self.p,ZZ),self.g,self.p,ZZ)
    def inv(self,x):
        u,v,g=gt.gf_gcdex(x,self.g,self.p,ZZ)
        assert g==[1], ('nonunit',len(x))
        return gt.gf_rem(u,self.g,self.p,ZZ)
    def unit(self,x):return gt.gf_gcd(x,self.g,self.p,ZZ)==[1]
    def at(self):return gt.gf_rem([1,0],self.g,self.p,ZZ)

class Tower:
    """Monic quotient of degree 2 or 3; coefficients ascend."""
    def __init__(self,K,gs):
        self.K=K;self.g=gs;self.d=len(gs)
        self.o=(K.o,)*self.d;self.i=self.lift(K.i)
        self.root=(K.o,K.i)+(K.o,)*(self.d-2)
    def lift(self,x):return (x,)+(self.K.o,)*(self.d-1)
    def c(self,n):return self.lift(self.K.c(n))
    def add(self,x,y):return tuple(self.K.add(a,b) for a,b in zip(x,y))
    def sub(self,x,y):return tuple(self.K.sub(a,b) for a,b in zip(x,y))
    def neg(self,x):return tuple(self.K.neg(a) for a in x)
    def mul(self,x,y):
        K=self.K;d=self.d
        out=[K.o]*(2*d-1)
        for i,a in enumerate(x):
            for j,b in enumerate(y):out[i+j]=K.add(out[i+j],K.mul(a,b))
        for i in range(2*d-2,d-1,-1):
            for j,b in enumerate(self.g):out[i-d+j]=K.sub(out[i-d+j],K.mul(out[i],b))
        return tuple(out[:d])

def det(K,m):
    return sumi(K,*(K.sub(prodi(K,m[0][i],m[1][(i+1)%3],m[2][(i+2)%3]),
         prodi(K,m[0][i],m[1][(i+2)%3],m[2][(i+1)%3])) for i in range(3)))

def contact(K,x,y,z,a,b,one):
    # x is the common extra, y left-exclusive, z right-exclusive.
    d=K.sub(one,b)
    l0=K.mul(K.sub(a,x),K.sub(a,y)); l1=K.neg(K.mul(x,y))
    r0=K.mul(K.sub(x,d),K.sub(z,d)); r1=K.neg(K.mul(K.sub(one,x),K.sub(one,z)))
    # For scaled roots the Gram parameters remain ordinary a,b; evaluate below.
    return l0,l1,r0,r1

def trim(K,a):
    u=list(a)
    while u and u[-1]==K.o:u.pop()
    return u
def rem(K,p,q):
    p=trim(K,p);q=trim(K,q)
    assert q
    l=K.inv(q[-1]);d=len(q)-1
    while len(p)>d:
        c=K.mul(p[-1],l);i=len(p)-1-d
        for j,val in enumerate(q):p[i+j]=K.sub(p[i+j],K.mul(c,val))
        p=trim(K,p)
    return p

def ev(K,cs,x):
    return reduce(lambda y,c:K.add(c,K.mul(y,x)),reversed(cs),K.o)


"""Exact local inverse-Gram coefficient-pivot fibers at dormant edge 8."""
import sympy as s
a,b,z=s.symbols('a b z')
N=s.Matrix([[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],
            [-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]])
D=s.Matrix([a**5*z**(i+1)-a**(i+1)*z**3*(6*z*z-15*a*z+10*a*a) for i in range(5)])
R0=s.Matrix([1]*5)
R1=s.Matrix([(1-b)**j-(b*j*(1-b)**(j-1) if j else 0) for j in range(5)])
f=s.factor((D.T*N*R0)[0]);g=s.factor((D.T*N*R1)[0])
A=s.cancel(f/(a*z*(a-z)))
B=s.cancel(g/(a*z*(a-z)))

Ah=s.Poly(A,z);Bh=s.Poly(B.subs(b,2-a),z)
res=s.resultant(Ah.as_expr(),Bh.as_expr(),z)
fs=s.factor_list(res,a)[1]
assert [(s.degree(f,a),k) for f,k in fs]==[(1,3),(1,12),(21,1)]
assert {s.expand(g) for g,k in fs if s.degree(g,a)==1}=={a,a-2}
F=s.Poly(fs[-1][0],a,domain=s.QQ)
line=s.Poly(s.subresultants(Ah.as_expr(),Bh.as_expr(),z)[-2],z)
assert line.degree()==1
l=s.Poly(line.nth(1),a,domain=s.QQ).rem(F);r=s.Poly(line.nth(0),a,domain=s.QQ).rem(F)
assert l.gcd(F).degree()==0
ze=(-r*l.invert(F)).rem(F)
def c(f):return s.Poly(f,a,domain=s.QQ).rem(F)
def evz(f):
    q=c(0)
    for u in s.Poly(f,z).all_coeffs():q=(q*ze+c(u)).rem(F)
    return q
assert not evz(A) and not evz(B.subs(b,2-a))
assert all(g.gcd(F).degree()==0 for g in [ze,ze-c(1),ze-c(a),ze-c(a/2),ze-c(a-1)])
X=s.Symbol('X')
P=s.Poly((X-a)*(X-a/2)*(X-a+1),X)
m=[c(sum(P.nth(i)/((i+j+2)*(i+j+3)) for i in range(4))) for j in range(6)]
E=[(m[j+1]-ze*m[j]).rem(F) for j in range(5)]
D=(E[0]*E[2]-E[1]*E[1]).rem(F)
assert D.gcd(F).degree()==0

F21, Z21 = F, ze

T4=lambda q:1-32*q+216*q*q-480*q**3+330*q**4
Uab=sum(m*a**i*b**j for i,row in enumerate(UU) for j,m in enumerate(row))
wd=(Uab-T4(a)*T4(b)).subs(b,2-a)
f=s.factor_list(wd,a)[1][-1][0]
assert s.cancel(wd/(-16*a*(a-2))-f)==0
f=s.Poly(f,a,domain=s.QQ)
assert f.degree()==6
j=s.Poly(s.rem((B-T4(b)*A).subs(b,2-a),f.as_expr(),a),z)
assert j.degree()==3
Qj,rj=s.div(j.as_expr(),z*(z-a),z)
assert s.rem(rj,f.as_expr(),a)==0
j=s.Poly(s.rem(Qj,f.as_expr(),a),z)
assert j.degree()==1
assert s.Poly(j.nth(1),a,domain=s.QQ).gcd(f).degree()==0


def setup(p):
    F=F21
    def red(u):
        n,d=u.as_numer_denom()
        return int(n)*pow(int(d),-1,p)%p
    g=[red(x) for x in F.all_coeffs()];assert g[0]
    K=Mod(g,p);a0=K.at()
    z0=ev(K,[K.c(red(x)) for x in reversed(Z21.all_coeffs())],a0)
    return K,a0,z0


class TP:
    def __init__(self,K):
        self.K=K;self.o=[];self.i=[K.i];self.t=[K.o,K.i]
    def lift(self,u):return trim(self.K,[u])
    def c(self,n):return self.lift(self.K.c(n))
    def add(self,p,q):
        K=self.K;n=max(len(p),len(q))
        return trim(K,[K.add(p[i] if i<len(p) else K.o,q[i] if i<len(q) else K.o) for i in range(n)])
    def neg(self,p):return [self.K.neg(x) for x in p]
    def sub(self,p,q):return self.add(p,self.neg(q))
    def mul(self,p,q):
        if not p or not q:return []
        K=self.K;s=[K.o]*(len(p)+len(q)-1)
        for i,x in enumerate(p):
            for j,y in enumerate(q):s[i+j]=K.add(s[i+j],K.mul(x,y))
        return trim(K,s)
    def gcd(self,p,q):
        K=self.K
        while q:p,q=q,rem(K,p,q)
        c=K.inv(p[-1]);return [K.mul(x,c) for x in p]
def momp(K,xs,n):
    f=[K.i]
    for u in xs:f=[K.sub(v,K.mul(u,w)) for v,w in zip([K.o]+f,f+[K.o])]
    return [sumi(K,*(K.mul(v,K.c(pow((i+j+2)*(i+j+3),-1,K.p))) for i,v in enumerate(f))) for j in range(n)]
def pair(K,u,v):
    return sumi(K,*(prodi(K,x,y,K.c(INV[i][j])) for i,x in enumerate(u) for j,y in enumerate(v)))

def testRight(p):
    K,a,z=setup(p)
    b=K.sub(K.c(2),a); d=K.sub(a,K.i); h=K.mul(a,K.c(pow(2,-1,p)))
    m=momp(K,[a,h,d],6); e=[K.sub(m[j+1],K.mul(z,m[j])) for j in range(5)]
    T0=TP(K);t=T0.t;A,Z,D,B=map(T0.lift,[a,z,d,b]);I=T0.i
    C=lambda x:T0.lift(x)
    ps=[T0.sub(C(e[j+1]),T0.mul(t,C(e[j]))) for j in range(4)]
    p0,p1,p2,p3=ps
    ds=T0.sub(T0.mul(p0,p2),T0.mul(p1,p1))
    sn=T0.sub(T0.mul(p0,p3),T0.mul(p1,p2))
    pn=T0.sub(T0.mul(p1,p3),T0.mul(p2,p2))
    homo=[T0.gcd(T0.gcd(ds,sn),pn)]
    # Psi coefficient matrix at u^x v^y.
    ln0=[T0.mul(A,T0.sub(A,t)),T0.neg(T0.sub(A,t))]
    ln1=[T0.o,T0.neg(t)]
    rn0=[T0.neg(T0.mul(D,T0.sub(t,D))),T0.sub(t,D)]
    rn1=[T0.neg(T0.sub(I,t)),T0.sub(I,t)]
    Ta,Tb=[pol(K,TT,v) for v in [a,b]]
    Uab=reduce(lambda v,cs:K.add(pol(K,cs,b),K.mul(v,a)),reversed(UU),K.o)
    def M(j,k):
        return sumi(T0,T0.mul(ln0[j],rn0[k]),prodi(T0,C(Ta),ln1[j],rn0[k]),
                    prodi(T0,C(Tb),ln0[j],rn1[k]),prodi(T0,C(Uab),ln1[j],rn1[k]))
    A0=sumi(T0,T0.mul(ds,M(0,0)),T0.mul(sn,M(0,1)),T0.mul(pn,M(1,1)))
    B0=T0.sub(M(1,0),M(0,1))
    hom1=T0.gcd(A0,B0)
    R=sumi(T0,T0.mul(A0,A0),prodi(T0,sn,A0,B0),prodi(T0,pn,ds,B0,B0))
    ah=T0.mul(ds,B0)
    L0=prodi(T0,T0.sub(A,t),T0.add(T0.mul(A,ah),A0));L1=T0.mul(t,A0)
    dr0=[K.i]+[K.o]*4
    dra=[prodi(K,K.c(i+1),powi(K,a,i)) for i in range(5)]
    re=lambda y:[K.mul(K.sub(K.i,y),powi(K,y,j)) for j in range(5)]
    aR=sumi(T0,T0.mul(L0,C(pair(K,dr0,re(d)))),T0.mul(L1,C(pair(K,dra,re(d)))))
    bR=sumi(T0,T0.mul(L0,C(pair(K,dr0,re(z)))),T0.mul(L1,C(pair(K,dra,re(z)))))
    Pa=lambda y:prodi(K,powi(K,y,3),sumi(K,prodi(K,K.c(6),y,y),K.neg(prodi(K,K.c(15),a,y)),prodi(K,K.c(10),a,a)))
    dv=[K.sub(prodi(K,powi(K,a,5),powi(K,z,i+1)),prodi(K,powi(K,a,i+1),Pa(z))) for i in range(5)]
    V0=pair(K,dv,re(z));V1=pair(K,dv,re(d))
    mx=lambda j:T0.sub(C(m[j+1]),T0.mul(t,C(m[j])))
    Int=T0.neg(sumi(T0,T0.mul(ds,mx(2)),T0.neg(T0.mul(sn,mx(1))),T0.mul(pn,mx(0))))
    prod=prodi(K,z,K.sub(z,K.i),K.sub(z,a),K.sub(z,h),K.sub(z,d))
    qz=sumi(T0,prodi(T0,C(K.mul(z,z)),ds),T0.neg(prodi(T0,Z,sn)),pn)
    W=prodi(T0,C(prod),T0.sub(Z,t),qz)
    Sd=T0.sub(prodi(T0,C(K.c(210)),Int,T0.sub(prodi(T0,aR,C(V0)),prodi(T0,bR,C(V1)))),
              prodi(T0,C(powi(K,a,5)),aR,W))
    gg=T0.gcd(R,Sd)

    items=[ds,sn,pn,A0,B0,R,Sd]
    assert [len(P)-1 for P in items]==[2,2,2,4,2,8,8]
    assert all(K.unit(P[-1]) for P in items)
    assert len(homo[0])==len(hom1)==len(gg)==1
    print('Right singular: degree21 coefficient algebra, all three exact local gcds are 1.')

def testLeft(p):
    def red(r):
        n,d=r.as_numer_denom()
        return int(n)*pow(int(d),-1,p)%p
    arr=[red(x) for x in f.all_coeffs()]
    assert arr[0]
    F=Mod(arr,p);a_=F.at()
    def eva(k):return ev(F,[F.c(red(x)) for x in reversed(s.Poly(k,a,domain=s.QQ).all_coeffs())],a_)
    cs=[eva(j.nth(k)) for k in range(2)]
    K=F;a0=a_;z0=K.neg(K.mul(cs[0],K.inv(cs[1])))
    b0=K.sub(K.c(2),a0); d0=K.sub(a0,K.i);h0=K.mul(a0,K.c(pow(2,-1,p)))
    m=momp(K,[a0,h0,d0],6);e=[K.sub(m[i+1],K.mul(z0,m[i])) for i in range(5)]
    T=TP(K); t=T.t; A,Z,D=map(T.lift,[a0,z0,d0]);one=T.i; C=T.lift
    Tb=C(pol(K,TT,b0))
    den=T.add(T.sub(t,D),T.mul(Tb,T.sub(one,t)))
    vn=T.add(T.mul(D,T.sub(t,D)),T.mul(Tb,T.sub(one,t)))
    xj=lambda es,i:T.sub(C(es[i+1]),T.mul(t,C(es[i])))
    ps=[T.sub(T.mul(den,xj(e,k+1)),T.mul(vn,xj(e,k))) for k in range(3)]
    p0,p1,p2=ps
    sd=T.gcd(T.gcd(p0,p1),p2)
    R=T.sub(T.mul(p0,p2),T.mul(p1,p1))
    l0=prodi(T,T.sub(A,t),T.sub(T.mul(A,p0),p1))
    l1=T.neg(T.mul(t,p1))
    dra=[prodi(K,K.c(i+1),powi(K,a0,i)) for i in range(5)]
    dr0=[K.i]+[K.o]*4
    re=lambda y:[K.mul(K.sub(K.i,y),powi(K,y,j)) for j in range(5)]
    aR=sumi(T,prodi(T,l0,C(pair(K,dr0,re(d0)))),prodi(T,l1,C(pair(K,dra,re(d0)))))
    bR=sumi(T,prodi(T,l0,C(pair(K,dr0,re(z0)))),prodi(T,l1,C(pair(K,dra,re(z0)))))
    C0=prodi(K,powi(K,z0,3),sumi(K,prodi(K,K.c(6),z0,z0),K.neg(prodi(K,K.c(15),a0,z0)),prodi(K,K.c(10),a0,a0)))
    dv=[K.sub(prodi(K,powi(K,a0,5),powi(K,z0,i+1)),prodi(K,powi(K,a0,i+1),C0)) for i in range(5)]
    V0=pair(K,dv,re(z0)); V1=pair(K,dv,re(d0))
    mx=lambda j:T.sub(T.mul(den,xj(m,j+1)),T.mul(vn,xj(m,j)))
    Int=T.neg(T.sub(T.mul(p0,mx(1)),T.mul(p1,mx(0))))
    prod=prodi(K,z0,K.sub(z0,K.i),K.sub(z0,a0),K.sub(z0,h0),K.sub(z0,d0))
    Dh=prodi(T,C(prod),T.sub(Z,t),T.sub(T.mul(den,Z),vn),T.sub(T.mul(p0,Z),p1))
    Sdiag=T.sub(prodi(T,C(K.c(210)),Int,T.sub(prodi(T,aR,C(V0)),prodi(T,bR,C(V1)))),
                prodi(T,C(powi(K,a0,5)),aR,Dh))
    G=T.gcd(R,Sdiag)

    assert [len(P)-1 for P in [p0,p1,p2,sd,R,Sdiag,G]]==[2,2,2,0,4,7,0]
    assert all(K.unit(P[-1]) for P in [p0,R,Sdiag])
    print('Left singular: degree6 coefficient algebra, consistency and diagonal gcds are 1.')

testRight(101)
testLeft(101)

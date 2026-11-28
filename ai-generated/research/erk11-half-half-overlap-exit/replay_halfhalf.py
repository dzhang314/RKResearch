"""Exact standalone replay of the ERK11 half-half-overlap exits.

Coefficient algebra over ZZ(a), exact gcds, and finite free mod-101 unit
receipts. Uses SymPy only; no sampled real or unknown-tableau reductions.
"""
from itertools import product
from math import lcm
from functools import reduce
import sympy as sym
from sympy import ZZ
from sympy.polys.rings import ring
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

def evaluate_contact(K,C,ap,bp):
    l0,l1,r0,r1=C
    U=reduce(lambda v,cs:K.add(pol(K,cs,bp),K.mul(v,ap)),reversed(UU),K.o)
    return sumi(K,K.mul(l0,r0),prodi(K,pol(K,TT,ap),l1,r0),
                prodi(K,pol(K,TT,bp),l0,r1),prodi(K,U,l1,r1))

def contacts_from_cubic(K,cs,a,b,M):
    # cs is monic scaled cubic. In the unscaled case M=1.
    L=Tower(K,cs);t=L.root
    S=L.neg(L.add(L.lift(cs[2]),t));P=L.add(L.lift(cs[1]),L.mul(t,L.neg(S)))
    E=Tower(L,[P,L.neg(S)]);u=E.root;v=E.sub(E.lift(S),u)
    il=lambda x:E.lift(L.lift(x))
    a0,b0=il(a),il(b);S1=il(M)
    C=contact(E,E.lift(t),u,v,E.mul(a0,S1),E.mul(b0,S1),S1)
    psi=evaluate_contact(E,C,a0,b0)
    A,B=psi
    n=L.add(L.add(L.mul(A,A),L.mul(S,L.mul(A,B))),L.mul(P,L.mul(B,B)))
    return L,S,P,A,B,n

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

def inner(K,x,y):
    return sumi(K,*(prodi(K,xx,yy,K.c(INV[i][j]))
            for i,xx in enumerate(x) for j,yy in enumerate(y) if xx and yy))
def bareP(K,ref,i,x):
    return K.mul(x,powi(K,K.sub(K.i,x) if ref else x,i))
def der(K,ref,i,x):
    b=K.sub(K.i,x) if ref else x
    if not ref:return prodi(K,K.c(i+1),powi(K,x,i))
    return K.sub(powi(K,b,i),prodi(K,x,K.c(i),powi(K,b,max(i-1,0))))

def anchor(K,a,z,x,w,ref):
    h=K.mul(a,K.c(pow(2,-1,K.p)))
    pa=lambda t:prodi(K,powi(K,t,3),sumi(K,prodi(K,K.c(6),powi(K,t,2)),
                            K.neg(prodi(K,K.c(15),a,t)),prodi(K,K.c(10),powi(K,a,2))))
    D=lambda y:[K.sub(prodi(K,powi(K,a,5),bareP(K,ref,i,y)),
                      K.mul(bareP(K,ref,i,a),pa(y))) for i in range(5)]
    aF=lambda n:prodi(K,powi(K,n,2),K.sub(a,n))
    l0=K.mul(K.sub(a,x),K.sub(a,z));l1=K.neg(K.mul(x,z))
    phi=[K.add(K.mul(l0,der(K,ref,i,K.o)),K.mul(l1,der(K,ref,i,a))) for i in range(5)]
    L=prodi(K,K.sub(w,a),K.sub(w,h),K.sub(h,a),aF(h))
    R=prodi(K,K.sub(w,a),K.sub(w,z),K.sub(z,a),aF(z))
    T=[K.sub(K.mul(L,x),K.mul(R,y)) for x,y in zip(D(z),D(h))]
    return [phi,D(w),T]


a0,x0=sym.symbols('a x')
b0=2-a0;d0=a0-1
P3=sym.Poly((x0-a0)*(x0-a0/2)*(x0-d0),x0)
ms=[sum(P3.nth(i)/((i+j+2)*(i+j+3)) for i in range(4)) for j in range(6)]
MS=sym.Matrix(3,3,lambda i,j:ms[i+j]); DD=sym.factor(MS.det())
Dp=sym.fraction(DD)[0]
qs=[sym.cancel(q) for q in (-MS.adjugate()*sym.Matrix(ms[3:]))/DD]
qr=[sym.Poly(sym.cancel(q*Dp),a0) for q in qs]; scale=2*lcm(*[int(c.q) for f in qr for c in f.all_coeffs()])
R,a=ring('a',ZZ); Y,y=ring('y',R);K=OverZ(R); b=2-a;d=a-1
dp=R.from_expr(Dp);M=scale*dp
r0,r1,r2=[R.from_expr((scale*z).as_expr()) for z in qr]
L=Tower(K,[M*M*r0,M*r1,r2]);W=L.root
S=L.neg(L.add(W,L.lift(r2)));P=L.add(L.lift(M*r1),L.mul(W,L.neg(S)))
A,B,C,ONE=map(L.lift,[M*a,M*b,M*d,M])
Ta=pol(L,TT,L.lift(a));Tb=pol(L,TT,L.lift(b))
Um=reduce(lambda v,cs:L.add(pol(L,cs,L.lift(b)),L.mul(v,L.lift(a))),reversed(UU),L.o)
def contactFrom(Cx):
    l0,l1,r0,r1=Cx
    return sumi(L,L.mul(l0,r0),prodi(L,Ta,l1,r0),prodi(L,Tb,l0,r1),prodi(L,Um,l1,r1))
def norm(p):
    v=L.mul(W,p);w=L.mul(W,v)
    return det(K,[p,v,w])
def quadNorm(E,z):
    A,B=z
    return sumi(L,L.mul(A,A),prodi(L,S,A,B),prodi(L,P,B,B))
def atProduct(a):
    return sumi(L,L.mul(a,a),L.neg(L.mul(a,S)),P)
def same():
    l0=atProduct(A);l1=L.neg(P);r0=atProduct(C)
    r1=L.neg(sumi(L,L.mul(ONE,ONE),L.neg(L.mul(ONE,S)),P))
    return norm(contactFrom((l0,l1,r0,r1)))
def different():
    _,_,_,_,_,p=contacts_from_cubic(K,L.g,a,b,M)
    return norm(p)
def plateauShared():
    E=Tower(L,[P,L.neg(S)])
    il=lambda x:E.lift(L.lift(x))
    a0,b0,m0=map(il,[a,b,M])
    rr=(E.lift(W),E.root,E.mul(a0,m0))
    cts=contact(E,*rr,E.mul(a0,m0),E.mul(b0,m0),m0)
    val=evaluate_contact(E,cts,a0,b0)
    return norm(quadNorm(E,val))
def plateauDisjoint():
    l0=atProduct(A);l1=L.neg(P)
    f=L.mul(L.sub(A,C),L.sub(W,C))
    g=L.neg(L.mul(L.sub(ONE,A),L.sub(ONE,W)))
    return norm(contactFrom((l0,l1,f,g)))
H=(y-a)*(2*y-a)*(y-d)*(M*y**3+r2*y**2+r1*y+r0)
J=-sum(sum(H.get((i,),0)*(840//((i-j+1)*(i-j+2))) for i in range(j+1,7))*y**j for j in range(6))
Xi=J*y*(1-y)*(a-y)*(y-d)
xi=[Xi.get((i,),0)*M**(9-i) for i in range(10)]
hv=R.from_expr((a*M).as_expr()/2)
def hcross():
    eqP=reduce(lambda w,c:w*hv+c,reversed(xi),R.zero)
    eqW=reduce(lambda w,c:L.add(L.mul(w,W),L.lift(c)),reversed(xi),L.o)
    return norm(L.sub(eqW,L.lift(eqP)))
def paircross():
    E=Tower(L,[P,L.neg(S)])
    e=reduce(lambda w,c:E.add(E.mul(w,E.root),E.lift(L.lift(c))),reversed(xi),E.o)
    return norm(e[1])
def prim(f):
    # Strip only exactly admissible nonzero scaling/width/plateau guards.
    assert f
    pool=[a,a-1,a-2,dp.exquo((a-1)**3)]
    u=f
    for q in pool:
        n=0
        while True:
            z,r=u.div(q)
            if r:break
            u=z;n+=1
    return u.primitive()[1]

Pz,az=R,a
pa=dp
ra0,ra1,ra2=r0,r1,r2
def asc(f):return [int(f.get((i,),0)) for i in range(f.degree()+1)]
Dr=asc(pa); Rs=list(map(asc,[ra0,ra1,ra2]))
def apply_div(K,f,g):
    if len(trim(K,f))>=len(trim(K,g)):
        return rem(K,f,g)
    return trim(K,f)
def solve_linear(K,f,nu):
    Q=trim(K,f); W=trim(K,nu)
    while len(W)>2:
        Q,W=W,rem(K,Q,W)
    assert len(W)==2
    return K.neg(K.mul(W[0],K.inv(W[1])))
def new_algebra(N,p):
    deg=N.degree();lc=int(N.LC)%p
    assert lc
    uni=[int(N.get((i,),0))*pow(lc,-1,p)%p for i in range(deg,-1,-1)]
    K0=Mod(uni,p); a=K0.at(); b=K0.sub(K0.c(2),a)
    inv=K0.inv(K0.mul(K0.c(scale),pol(K0,Dr,a)))
    gs=[K0.mul(pol(K0,V,a),inv) for V in Rs]
    return K0,a,b,gs
def diag_kind(K,a,b,l,r,m,need,right_repeat=[]):
    # l/r = local extra clock choices kept in ordinary coordinates.
    opp=lambda x:K.sub(K.i,x)
    L={(i,j):anchor(K,a,l[i],l[1-i],w,False) for i in [0,1] for j,w in enumerate(m)}
    R={(i,j):anchor(K,b,opp(r[i]),opp(r[1-i]),opp(w),True) for i in [0,1] for j,w in enumerate(m)}
    good=[]
    for i,k,j,l in product(range(2),range(2),range(3),range(3)):
        if j==l: continue
        u,v=L[i,j],R[k,l]
        assert inner(K,u[0],v[0])==K.o
        if j in need:
            gate=inner(K,u[1],v[0]); tag='repeat'
        elif l in right_repeat:
            gate=inner(K,u[0],v[1]); tag='right-repeat'
        else:
            gate=det(K,[[inner(K,s,t) for t in v] for s in u]); tag='det'
        ok=K.unit(gate)
        if not ok: raise ValueError((i,k,j,l,tag))
        good.append(tag)
    return (good.count('repeat'),good.count('right-repeat'),good.count('det'))

def testA(N,p):
    K,a,b,gs=new_algebra(N,p)
    L,S,P,A,B,nu=contacts_from_cubic(K,gs,a,b,K.i)
    t=solve_linear(K,gs+[K.i],nu)
    assert ev(K,gs+[K.i],t)==K.o and ev(K,nu,t)==K.o
    u=K.neg(K.mul(ev(K,A,t),K.inv(ev(K,B,t))))
    v=K.sub(ev(K,S,t),u)
    h=K.mul(a,K.c(pow(2,-1,p)))
    assert not K.add(K.sub(K.mul(u,u),K.mul(ev(K,S,t),u)),ev(K,P,t))
    return [diag_kind(K,a,b,[t,u],[t,v],[r,u,v],[0,1],[0]) for r in [h,t]]

class Quad(Tower):
    def __init__(self,K,g):
        super().__init__(K,g)
        self.p=K.p
    def unit(self,x):
        A,B=x
        nu=sumi(self.K,self.K.mul(A,A),prodi(self.K,self.K.neg(self.g[1]),A,B),prodi(self.K,self.g[0],B,B))
        return self.K.unit(nu)

def testB(N,p):
    K,a,b,gs=new_algebra(N,p)
    d=K.sub(K.i,b)
    L=Tower(K,gs);t=L.root;S=L.neg(L.add(t,L.lift(gs[2])));P=L.add(L.lift(gs[1]),L.mul(t,L.neg(S)))
    a0,b0,d0=map(L.lift,[a,b,d])
    q=lambda z:sumi(L,L.mul(z,z),L.neg(L.mul(z,S)),P)
    l0=q(a0);l1=L.neg(P);r0=L.mul(L.sub(a0,d0),L.sub(t,d0));r1=L.neg(L.mul(L.sub(L.i,a0),L.sub(L.i,t)))
    nu=evaluate_contact(L,(l0,l1,r0,r1),a0,b0)
    tv=solve_linear(K,gs+[K.i],nu)
    assert ev(K,gs+[K.i],tv)==K.o and ev(K,nu,tv)==K.o
    R=Quad(K,[ev(K,P,tv),K.neg(ev(K,S,tv))]); u=R.root;v=R.sub(R.lift(ev(K,S,tv)),u)
    aa,bb,tt=map(R.lift,[a,b,tv])
    return diag_kind(R,aa,bb,[u,v],[aa,tt],[u,v,tt],[0,1])



def main():
    xh=prim(hcross()); xp=prim(paircross())
    ns,nd,nh,np=[prim(f()) for f in [same,different,plateauShared,plateauDisjoint]]
    assert [s.degree() for s in [ns,nd,nh,np,xh,xp]]==[54,108,96,48,42,20]
    assert all(m.gcd(n).degree()==0 for m,n in [(ns,xh),(ns,xp),(nd,xh),(nh,xh)])
    print('Half-half two-plus exact residual norm gcds: 4 coprime cases.')
    assert testA(nd,101)==[(16,4,4),(16,4,4)]
    assert testB(np,101)==(16,0,8)
    print('Half-half one-cross exact units: 48 different-extra + 24 opposite-plateau schedules.')
if __name__=='__main__':main()

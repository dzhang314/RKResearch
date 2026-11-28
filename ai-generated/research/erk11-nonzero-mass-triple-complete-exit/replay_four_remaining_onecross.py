"""Exact standalone replay for the last four nonzero-mass ERK11 one-cross charts.

The integer and rational projection algebra is rebuilt from the moment
polynomials, not read from a serialized numerical parameter file. SymPy
is required; NumPy is optional for exact bounded-integer modular products.
"""
from itertools import product
from functools import reduce
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


"""Explore the four-distinct same-free-pair crossover equations over Q."""
import sympy as s
from sympy.polys.rings import ring
from sympy import QQ
a,b=s.symbols('a b')
R,aa,bb=ring('a,b',QQ)
X,x=ring('x',R)
P=(x-aa)*(x-aa/2)*(x+bb-1)*(x+bb/2-1)
def it(i):
    return sum(P.get((j,),0)/((i+j+2)*(i+j+3)) for j in range(5))
m=[it(i) for i in range(5)]
m0,m1,m2,m3,m4=m
D=m0*m2*m4+2*m1*m2*m3-m0*m3**2-m1**2*m4-m2**3
DL=m0*m2-m1**2
U=m1*m2-m0*m3;V=m1*m3-m2*m2
l0=aa**2*DL+aa*U+V;l1=-V
d=1-bb;r0=d*d*DL+d*U+V;r1=-DL-U-V
T=lambda a:1-32*a+216*a*a-480*a**3+330*a**4
UC=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
PGRAM=sum(t*aa**i*bb**j for i,r in enumerate(UC) for j,t in enumerate(r))
C1=l0*r0+T(aa)*l1*r0+T(bb)*l0*r1+PGRAM*l1*r1

Y=x
pair=Y*Y+U*Y+DL*V
h=aa/2;e=1-bb/2
lBoth=(aa**2*DL+aa*U+V,-V)
rBoth=(d*d*DL+d*U+V,-DL-U-V)
def lc(y,z):
    return (DL*aa-y)*(DL*aa-z),-y*z
def rc(y,z):
    return (y-DL*d)*(z-DL*d),-(DL-y)*(DL-z)
def form(l,r):
    l0,l1=l;r0,r1=r
    c=X(l0*r0+T(aa)*l1*r0+T(bb)*l0*r1+PGRAM*l1*r1).rem(pair)
    return c.get((0,),R.zero),c.get((1,),R.zero)
def nrm(cs):
    g,h=cs
    return g*g-U*g*h+DL*V*h*h
def trim_delta(c):
    assert c
    while True:
        q,r=c.div(DL)
        if r:return c
        c=q
def prim(c):return s.Poly(c.as_expr(),a,b).clear_denoms()[1].primitive()[1].as_expr()
rows=[('asym',form(lc(DL*e,Y),rBoth)),
      ('opposite-half',form(lBoth,rc(DL*aa,DL*h))),
      ('opposite-shared-free',form(lBoth,rc(DL*aa,Y))),
      ('opposite-disjoint-free',form(lc(DL*e,-U-Y),rc(DL*aa,Y)))]
DA,DEL=prim(D),prim(DL)
guard=[a,b,a-1,a-2,b-1,b-2,a+b-1,a+b-2,2*a+b-2,a+2*b-2,DEL]
def eval_clear(p,f,l,r):
    a0=s.Poly(0,a,domain=s.QQ)
    pp=s.Poly(p,b)
    if pp.degree()==0:
        return s.Poly(p,a,domain=s.QQ).rem(f)
    ls=[s.Poly(1,a,domain=s.QQ)];rs=ls.copy()
    for _ in range(pp.degree()):
        ls.append((ls[-1]*l).rem(f));rs.append((rs[-1]*(-r)).rem(f))
    for i in range(pp.degree()+1):
        a0=(a0+s.Poly(pp.nth(i),a,domain=s.QQ)*ls[pp.degree()-i]*rs[i]).rem(f)
    return a0


exponents={
 'asym':(252,[(1,12),(4,3),(6,2),(20,3),(156,1)]),
 'opposite-half':(108,[(1,6),(4,1),(6,1),(20,1),(72,1)]),
 'opposite-shared-free':(252,[(1,12),(4,3),(6,2),(20,3),(156,1)]),
 'opposite-disjoint-free':(216,[(1,12),(4,2),(6,2),(20,2),(144,1)]),
}
keep=[]
for name,xy in rows:
    c=xy[0] if not xy[1] else nrm(xy)
    c=prim(trim_delta(c))
    sr=s.subresultants(DA,c,b)
    r0=sr[-1]
    assert s.degree(r0,b)==0
    line=s.Poly(sr[-2],b)
    assert line.degree()==1
    L=s.Poly(line.nth(1),a,domain=s.QQ)
    Rr=s.Poly(line.nth(0),a,domain=s.QQ)
    pfs=s.factor_list(r0,a)[1]
    assert (s.degree(r0,a),[(s.degree(f,a),n) for f,n in pfs])==exponents[name]
    retained=[]
    for f,k in pfs:
        F=s.Poly(f,a,domain=s.QQ)
        if F.degree()==1:
            assert F==s.Poly(a,a,domain=s.QQ)
            continue
        l=L.rem(F);r=Rr.rem(F)
        assert l
        if F.degree() in [4,6,20]:
            assert F.gcd(l).degree()==0
            assert not eval_clear(b if F.degree()==6 else DEL,F,l,r)
            continue
        retained.append((F.as_expr(),l.as_expr(),r.as_expr()))
    assert len(retained)==1
    assert s.degree(retained[0][0],a)==exponents[name][1][-1][0]
    keep.append((name,retained[0]))
    print('Exact contact projection',name,'live degree',s.degree(retained[0][0],a),flush=True)

try:
    import numpy as np
except ImportError:
    np=None
class FastMod(Mod):
    def __init__(self,g,p):
        super().__init__(g,p)
        n=len(g)-1
        assert n*(p-1)**2 < 2**55
        self.n=n
        if np is None:return
        z=np.array([(-g[n-i]*pow(g[0],-1,p))%p for i in range(n)],dtype=np.int64)
        zi=z.copy()
        self.map=[]
        for _ in range(n-1):
            self.map.append(zi)
            zi=(np.append(0,zi[:-1])+zi[-1]*z)%p
        self.map=np.stack(self.map) if self.map else np.zeros((0,n),np.int64)
    def mul(self,a,b):
        if np is None:return super().mul(a,b)
        if not a or not b:return []
        p,n=self.p,self.n
        v=np.convolve(np.array(a[::-1],dtype=np.int64),np.array(b[::-1],dtype=np.int64))%p
        if len(v)<=n:
            u=v
        else:
            u=(v[:n]+v[n:]@self.map[:len(v)-n])%p
        return list(map(int,np.trim_zeros(u,'b')[::-1]))


class Quad(Tower):
    def __init__(self,K,g):
        super().__init__(K,g);self.p=K.p
    def nrm(self,x):
        A,B=x
        return sumi(self.K,self.K.mul(A,A),prodi(self.K,self.K.neg(self.g[1]),A,B),prodi(self.K,self.g[0],B,B))
    def unit(self,x):return self.K.unit(self.nrm(x))
    def inv(self,x):
        A,B=x
        d=self.K.inv(self.nrm(x))
        return (self.K.mul(d,self.K.sub(A,self.K.mul(self.g[1],B))),self.K.neg(self.K.mul(d,B)))

def mom(K,cl):
    f=[K.i]
    for x in cl:
        f=[K.sub(s,K.mul(x,t)) for s,t in zip([K.o]+f,f+[K.o])]
    return [sumi(K,*(K.mul(v,K.c(pow((i+j+2)*(i+j+3),-1,K.p))) for i,v in enumerate(f))) for j in range(4)]

def score(K,a,b,l,r,m,rightrep=[]):
    opp=lambda t:K.sub(K.i,t)
    L={(i,j):anchor(K,a,l[i],l[1-i],w,False) for i in [0,1] for j,w in enumerate(m)}
    R={(i,j):anchor(K,b,opp(r[i]),opp(r[1-i]),opp(w),True) for i in [0,1] for j,w in enumerate(m)}
    hits=[0,0,0]
    for i,k,j,n in product(range(2),range(2),range(3),range(3)):
        if j==n:continue
        U,V=L[i,j],R[k,n]
        if j in [0,1]:
            gate=inner(K,U[1],V[0]);s=0
        elif n in rightrep:
            gate=inner(K,U[0],V[1]);s=1
        else:
            gate=det(K,[[inner(K,x,y) for y in V] for x in U]);s=2
        if not K.unit(gate):raise ValueError((i,k,j,n,s))
        hits[s]+=1
    return tuple(hits)
def test(name,f,l,r,p):
    aa=sym.Symbol('a')
    F=sym.Poly(f,aa,domain=sym.QQ)
    def tm(x):
        n,d=x.as_numer_denom()
        return int(n)*pow(int(d),-1,p)%p
    coeff=[tm(x) for x in F.all_coeffs()]
    assert coeff[0]
    A=FastMod(coeff,p);a=A.at()
    vv=lambda z:ev(A,[A.c(tm(x)) for x in reversed(sym.Poly(z,aa,domain=sym.QQ).all_coeffs())],a)
    b=A.neg(A.mul(vv(r),A.inv(vv(l))))
    half=A.c(pow(2,-1,p));h=A.mul(half,a);d=A.sub(A.i,b);e=A.sub(A.i,A.mul(half,b))
    # mom() expects Quad.p; Mod.p also supplies it.
    m0,m1,m2,m3=mom(A,[a,h,d,e])
    dl=A.sub(A.mul(m0,m2),A.mul(m1,m1));di=A.inv(dl)
    qa=A.mul(di,A.sub(A.mul(m1,m2),A.mul(m0,m3)))
    qb=A.mul(di,A.sub(A.mul(m1,m3),A.mul(m2,m2)))
    E=Quad(A,[qb,qa]);t=E.root;u=E.neg(E.add(E.lift(qa),t))
    aa,bb,hh,dd,ee=map(E.lift,[a,b,h,d,e])
    if name=='opposite-half':
        return [score(E,aa,bb,[t,u],[aa,hh],[t,u,ee])]
    if name=='asym':
        C=contact(E,t,ee,u,aa,bb,E.i)
        # Generic contact helper uses first root on both fronts, and allows e as second left root.
    elif name=='opposite-shared-free':
        l0=E.mul(E.sub(aa,t),E.sub(aa,u));l1=E.neg(E.mul(t,u))
        r0=E.mul(E.sub(aa,dd),E.sub(t,dd));r1=E.neg(E.mul(E.sub(E.i,aa),E.sub(E.i,t)))
        C=(l0,l1,r0,r1)
    else:
        l0=E.mul(E.sub(aa,ee),E.sub(aa,u));l1=E.neg(E.mul(ee,u))
        r0=E.mul(E.sub(aa,dd),E.sub(t,dd));r1=E.neg(E.mul(E.sub(E.i,aa),E.sub(E.i,t)))
        C=(l0,l1,r0,r1)
    x,y=evaluate_contact(E,C,aa,bb)
    t=A.neg(A.mul(x,A.inv(y)));u=A.neg(A.add(qa,t))
    assert A.add(A.add(A.mul(t,t),A.mul(qa,t)),qb)==A.o
    if name=='asym':return [score(A,a,b,[e,t],[t,u],[v,h,u],[0]) for v in [e,t]]
    if name=='opposite-shared-free':return [score(A,a,b,[t,u],[a,t],[h,u,e])]
    return [score(A,a,b,[e,u],[a,t],[h,u,t])]



for name,fx in keep:
    expected=[(16,4,4),(16,4,4)] if name=='asym' else [(16,0,8)]
    ans=test(name,*fx,101)
    assert ans==expected
    print('Exact mod101 unit contacts',name,ans,flush=True)

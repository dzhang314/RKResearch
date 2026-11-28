"""Exact standalone replay of the four-distinct same-extras one-cross exit."""
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

S,T=s.symbols('S T')
def to_sym(p):
    z,r,_=s.symmetrize(p.as_expr(),[a,b],formal=True)
    assert not r
    return s.Poly(z.subs({s.Symbol('s1'):S,s.Symbol('s2'):T}),S,T).clear_denoms()[1].primitive()[1].as_expr()
D,DL,C1=map(to_sym,[D,DL,C1])
r0=s.resultant(D,C1,T)
assert s.degree(r0,S)==72
assert [(s.degree(f,S),m) for f,m in s.factor_list(r0,S)[1]]==[(4,1),(6,1),(10,2),(42,1)]

sub=s.subresultants(D,C1,T)
h=s.Poly(sub[-2],T)
assert h.degree()==1
L=s.Poly(h.nth(1),S,domain=s.QQ);R=s.Poly(h.nth(0),S,domain=s.QQ)
out=[]
for f,n in s.factor_list(r0,S)[1]:
    fq=s.Poly(f,S,domain=s.QQ)
    lr=L.rem(fq);rr=R.rem(fq)
    assert lr
    if fq.degree()==42:
        out.append((f,lr.as_expr(),rr.as_expr()))
        print("degree-42 live line saved without rational inversion",flush=True)
        continue
    v=(-rr*lr.invert(fq)).rem(fq)
    de=s.Poly(DL,T)
    dl=s.Poly(0,S,domain=s.QQ)
    for c in de.all_coeffs():dl=(dl*v+s.Poly(c,S,domain=s.QQ)).rem(fq)
    print('factor S degree',fq.degree(),'Tzero',not v,'Deltazero',not dl,flush=True)
    assert (not v if fq.degree()==6 else not dl)

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
def second(K,a,b,t,p,h,e):
    slots=[p,h,e];reverse=lambda x:K.sub(K.i,x)
    left=[t,p];right=[t,p]
    L={(i,j):anchor(K,a,left[i],left[1-i],w,False) for i in [0,1] for j,w in enumerate(slots)}
    R={(i,j):anchor(K,b,reverse(right[i]),reverse(right[1-i]),reverse(w),True) for i in [0,1] for j,w in enumerate(slots)}
    scores=[0,0,0]
    for i,k,j,l in product(range(2),range(2),range(3),range(3)):
        if j==l: continue
        U,V=L[i,j],R[k,l]
        tag=0 if j in [0,1] else (1 if l==0 else 2)
        if tag==0:G=inner(K,U[1],V[0])
        elif tag==1:G=inner(K,U[0],V[1])
        else:G=det(K,[[inner(K,x,y) for y in V] for x in U])
        if not K.unit(G): raise ValueError((i,k,j,l,tag))
        scores[tag]+=1
    return scores
def test(f,l,r,pr):
    ff=sym.Poly(f,S,domain=sym.QQ)
    def to_mod(x):
        num,den=x.as_numer_denom()
        return int(num)*pow(int(den),-1,pr)%pr
    coeff=[to_mod(x) for x in ff.all_coeffs()]
    assert coeff[0]
    base=Mod(coeff,pr);s=base.at()
    vv=lambda y:ev(base,[base.c(to_mod(x)) for x in reversed(sym.Poly(y,S,domain=sym.QQ).all_coeffs())],s)
    tv=base.neg(base.mul(vv(r),base.inv(vv(l))))
    L=Quad(base,[tv,base.neg(s)])
    a=L.root;b=L.sub(L.lift(s),a)
    half=L.c(pow(2,-1,pr))
    h=L.mul(half,a);d=L.sub(L.i,b);e=L.sub(L.i,L.mul(half,b))
    m0,m1,m2,m3=mom(L,[a,h,d,e])
    dl=L.sub(L.mul(m0,m2),L.mul(m1,m1));di=L.inv(dl)
    ua=L.mul(di,L.sub(L.mul(m1,m2),L.mul(m0,m3)))
    va=L.mul(di,L.sub(L.mul(m1,m3),L.mul(m2,m2)))
    E=Quad(L,[va,ua]);p=E.root;t=E.neg(E.add(E.lift(ua),p))
    return second(E,E.lift(a),E.lift(b),t,p,E.lift(h),E.lift(e))


assert len(out)==1 and s.degree(out[0][0],S)==42
assert test(*out[0],101)==[16,4,4]
print('Exact degree-42 ring: 16 left repeat, 4 right repeat, 4 determinant units.')

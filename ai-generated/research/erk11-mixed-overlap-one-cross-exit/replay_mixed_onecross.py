"""Standalone algebraic replay of the mixed-overlap one-cross exclusion.

Exact ZZ[a] coefficient multiplication builds the degree-108 first contact
factor.  Then the finite free algebra is checked modulo 101; no candidate
tableau entries are reduced.  Requires SymPy only.
"""
from itertools import product
from operator import add
from functools import reduce
import sympy as sym
from sympy import ZZ
from sympy.polys.rings import ring
from sympy.polys import galoistools as gt

D0=[-476,6624,-40926,145804,-328125,482244,-462126,278124,-95256,14112]
R0=[5632,-70164,385608,-1223709,2465496,-3264222,2835108,-1555092,487872,-66528]
R1=[-32760,430128,-2502090,8404080,-17877054,24900036,-22663998,12978504,-4235616,598752]
R2=[57600,-782532,4717248,-16407822,36086820,-51880626,48666744,-28684656,9624384,-1397088]
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

def first_contact_factor():
    R,a=ring('a',ZZ); K=OverZ(R);b=2-2*a
    D=pol(K,D0,a);M=66*D
    r0,r1,r2=[pol(K,z,a) for z in [R0,R1,R2]]
    L,S,P,A,B,n=contacts_from_cubic(K,[M*M*r0,M*r1,r2],a,b,M)
    n1=L.mul(L.root,n);n2=L.mul(L.root,n1)
    out=det(K,[n,n1,n2])
    assert out.degree()==264
    q=out.exquo(a**6*(a-1)**6*D**16)
    assert q.degree()==108
    return q.primitive()[1]

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

def second_contacts(K,a,b,t,u,v):
    h=K.mul(a,K.c(pow(2,-1,K.p)))
    slots=[h,u,v];opp=lambda t:K.sub(K.i,t)
    L={(lu,j):anchor(K,a,u if lu else t,t if lu else u,w,False)
          for lu in [0,1] for j,w in enumerate(slots)}
    R={(rv,j):anchor(K,b,opp(v if rv else t),opp(t if rv else v),opp(w),True)
          for rv in [0,1] for j,w in enumerate(slots)}
    hits=[]
    for lu,rv,j,k in product(range(2),range(2),range(3),range(3)):
        if j==k:continue
        ls,rs=L[lu,j],R[rv,k]
        assert inner(K,ls[0],rs[0])==K.o
        if j in (0,1):
            gate=inner(K,ls[1],rs[0])
            tag='repeat'
        else:
            gate=det(K,[[inner(K,l,r) for r in rs] for l in ls])
            tag='3by3'
        assert K.unit(gate),(lu,rv,j,k,tag)
        hits.append(tag)
    assert hits.count('repeat')==16 and hits.count('3by3')==8
    return hits

def check():
    n=first_contact_factor()
    mod=101
    deg=n.degree()
    lc=int(n.LC)%mod
    assert deg==108 and lc
    g=[int(n.get((i,),0))*pow(lc,-1,mod)%mod for i in range(deg,-1,-1)]
    K=Mod(g,mod);a=K.at()
    b=K.sub(K.c(2),K.mul(K.c(2),a))
    Minv=K.inv(K.mul(K.c(66),pol(K,D0,a)))
    gs=[K.mul(pol(K,r,a),Minv) for r in [R0,R1,R2]]
    L,S,P,A,B,nu=contacts_from_cubic(K,gs,a,b,K.i)
    q=gs+[K.i]
    assert len(trim(K,nu))==3
    lr=rem(K,q,nu)
    assert len(lr)==2
    t=K.neg(K.mul(lr[0],K.inv(lr[1])))
    assert ev(K,q,t)==K.o and ev(K,nu,t)==K.o
    u=K.neg(K.mul(ev(K,A,t),K.inv(ev(K,B,t))))
    v=K.sub(ev(K,S,t),u)
    assert K.add(K.sub(K.mul(u,u),K.mul(ev(K,S,t),u)),ev(K,P,t))==K.o
    hits=second_contacts(K,a,b,t,u,v)
    print('First-contact degree',deg,'leading residue',lc,
          '| live mod101 pivots |',len(hits),'unit second gates')

if __name__=='__main__':check()

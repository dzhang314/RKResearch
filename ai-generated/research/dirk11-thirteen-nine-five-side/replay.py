#!/usr/bin/env python3
"""Exact Volterra-pivot exclusion of either five-dirty-side DIRK11/13 face.

This builds the denominator-cleared degree-188 resultant over Q, removes
six lower factor guards, and checks a finite-free quotient at 23.
All calculations use exact integers/rationals and finite-field arithmetic.
"""
import sympy as sy
from pathlib import Path
from sympy.polys.agca.extensions import FiniteExtension
x,s,p,E=sy.symbols('X S P E')
J4=42*x**4-84*x**3+56*x**2-14*x+1
J5=(2*x-1)*(66*x**4-132*x**3+84*x**2-18*x+1)
G=x*(462*x**5-1260*x**4+1260*x**3-560*x**2+105*x-6)
C=x*x-s*x+p
q4,r4=sy.div(J4,C,x);q5,r5=sy.div(J5,C,x)
r40,r41=(sy.expand(r4).coeff(x,i)for i in range(2))
r50,r51=(sy.expand(r5).coeff(x,i)for i in range(2))
D=sy.Poly(r40*r51-r41*r50,s,p,domain=sy.QQ).primitive()[1].as_expr()
def px(*a):print(*a,flush=True)
def ip(f,vars):
    return sy.Poly(f,*vars,domain=sy.QQ).clear_denoms()[1].primitive()[1].as_expr()
def int0(f):
    return sum(a*x**(i+1)/(i+1)for (i,),a in sy.Poly(f,x).terms())
a,b,c=sy.symbols('u v w')
U=x**3+a*x*x+b*x+c
I0=int0(x*U);I1=int0(x*x*U)
def col(f):
    q=sy.rem(f,U,x)
    return [sy.expand(q).coeff(x,i)for i in range(3)]
M,N,S,T=map(col,(I0,x*I0,I1,G))
d0=sy.expand(sy.Matrix.hstack(*map(sy.Matrix,[M,N,S])).det())
d1=sy.expand(sy.Matrix.hstack(*map(sy.Matrix,[M,N,T])).det())
px('universal D0/D1',*(len(sy.Poly(j,a,b,c).terms())for j in (d0,d1)))
def reduceD(f):
    return sy.rem(sy.expand(f),D,p)
def ringmul(f,g):return reduceD(f*g)
def ringpowers(f,n):
    powers=[sy.Integer(1)]
    for _ in range(n):powers.append(ringmul(powers[-1],f))
    return powers

def chart(h,j,k):
    us=sy.expand(h*q5-j*q4)
    d=sy.expand(us.coeff(x,3))
    u2,u1,u0=(sy.expand(us.coeff(x,i))for i in [2,1,0])
    m0=sy.Poly(d0,a,b,c).total_degree()
    m1=sy.Poly(d1,a,b,c).total_degree()
    MM=max(m0,m1+1)
    p0,p1,p2,p3=map(lambda v:ringpowers(v,MM),(d,u2,u1,u0))
    def hom(f,m):
        out=0
        for (i,j,k),r in sy.Poly(f,a,b,c).terms():
            v1=ringmul(p1[i],p2[j])
            v2=ringmul(p3[k],p0[m-i-j-k])
            out+=r*ringmul(v1,v2)
        return sy.expand(out)
    D0=hom(d0,MM)
    D1=hom(d1,MM-1)
    C0=sy.rem(G,C,x)
    C1=sy.rem(int0(x*x*us)-x*int0(x*us),C,x)
    A=reduceD(C0.coeff(x,0)*D0-C1.coeff(x,0)*D1)
    B=reduceD(C0.coeff(x,1)*D0-C1.coeff(x,1)*D1)
    F=ip(A+x*B,(x,s,p))
    A,B=F.coeff(x,0),F.coeff(x,1)
    px('chart',k,'aff vector degrees',sy.Poly(F,x,s,p).total_degree())
    L=ip(reduceD(A*A+s*A*B+p*B*B),(s,p))
    pp=sy.resultant(D,L,p)
    px('chart',k,'resultant degree',sy.degree(pp,s))
    return F,L,pp

def create(poly,vars,K,c):
    if not vars:return K.from_sympy(poly)
    ans=K.zero
    for mon,a in sy.Poly(poly,*vars,domain=sy.QQ).terms():
        z=K.from_sympy(a)
        for t,k in zip(c,mon):z*=t**k
        ans+=z
    return ans

def dense(expr,w,K,vars,c):
    P=sy.Poly(expr,w)
    return [create(P.nth(i),vars,K,c)for i in range(P.degree()+1)]

def trim(a,K):
    a=list(a)
    while a and a[-1]==K.zero:a.pop()
    return a

def rem(a,b,K):
    a=trim(a,K);b=trim(b,K)
    assert b
    while len(a)>=len(b):
        t=a[-1]/b[-1];assert t*b[-1]==a[-1];j=len(a)-len(b)
        for i,v in enumerate(b):a[i+j]-=t*v
        a=trim(a,K)
    return a

def euclid(a,b,K):
    a=trim(a,K);b=trim(b,K)
    while b:a,b=b,rem(a,b,K)
    return [c/a[-1]for c in a] if a else []

def scale(a,d,K):return trim([x*d for x in a],K)
def add(a,b,K):
    n=max(len(a),len(b))
    return trim([(a[i] if i<len(a)else K.zero)+(b[i]if i<len(b)else K.zero)for i in range(n)],K)
def integ(f,K):return [K.zero]+[v/K.convert(i+1)for i,v in enumerate(f)]
def at(V,i,K):return V[i]if i<len(V)else K.zero


def K_alg(f,var):
    return sy.QQ.algebraic_field((sy.Poly(f,var),var))

def embed(q,var,f,K):
    co=sy.Poly(sy.rem(q,f,var),var,domain=sy.QQ).all_coeffs()
    return K([sy.QQ.convert(c)for c in co])

def split_univariate(A,ff,K):
    pA=sy.Poly(A,p)
    return [embed(pA.nth(k),s,ff,K)for k in range(pA.degree()+1)]

def det3(U,V,W,K):
    a,b,c=[[at(z,k,K)for k in range(3)]for z in (U,V,W)]
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])

def ev(f,z,K):
    out=K.zero
    for c in reversed(f):out=out*z+c
    return out

def base_data(sv,pv,d,j,K):
    guard=create(d,(s,p),K,(sv,pv)); rhs=create(j,(s,p),K,(sv,pv))
    assert guard!=K.zero
    U=add(scale(dense(q5,x,K,[s,p],[sv,pv]),guard,K),
          scale(dense(q4,x,K,[s,p],[sv,pv]),-rhs,K),K)
    assert len(U)==4
    A0=integ([K.zero]+U,K);A1=integ([K.zero,K.zero]+U,K)
    GG=dense(G,x,K,[],[])
    aa=rem(A0,U,K);bb=rem([K.zero]+A0,U,K)
    D0=det3(aa,bb,rem(A1,U,K),K)
    D1=det3(aa,bb,rem(GG,U,K),K)
    return A0,A1,GG,D0,D1

def slope_zero():
    Q99=99*s**4-396*s**3+573*s**2-354*s+79
    assert sy.expand(r41-14*(s-1)*(-6*p+3*s*s-3*s+1))==0
    Qp=132*p*p-36*p+2
    assert sy.expand(r51.subs(s,1)-Qp)==0
    pfun=(3*s*s-3*s+1)/6
    assert sy.expand(r51.subs(p,pfun)+Q99/3)==0
    for tag,mod,var in [('S=1',Qp,p),('S!=1',Q99,s)]:
        K=K_alg(mod,var)
        sv,pv=(K.one,K.unit)if tag=='S=1'else(K.unit,(K(3)*K.unit*K.unit-K(3)*K.unit+K.one)/K(6))
        A0,A1,GG,D0,D1=base_data(sv,pv,r40,r50,K)
        F=add(scale(GG,D0,K),scale(add(A1,scale([K.zero]+A0,-K.one,K),K),-D1,K),K)
        # This chart is excluded by the affine determinant alone.
        assert len(euclid([pv,-sv,K.one],F,K))==1
        px('exact zero-slope',tag,'affine gcd degree 0')

def candidate60(N,R):
    coeff,fs=sy.factor_list(R,s)
    assert sorted((sy.degree(g,s),m)for g,m in fs)==[(1,28),(4,1),(4,2),(4,14),(6,2),(10,2),(60,1)]
    assert sy.expand(R-coeff*sy.prod(g**m for g,m in fs))==0
    U=sy.expand(r41*q5-r51*q4)
    tests=[('zero slope',r41),('origin clean',p),('terminal clean',1-s+p),('cubic origin',U.coeff(x,0)),
           ('G at a clean clock',sy.resultant(G,C,x))]
    out=None
    for ff,m in fs:
        n=sy.degree(ff,s)
        if n==60:
            out=ff
            continue
        K=K_alg(ff,s)
        pD=split_univariate(D,ff,K);pN=split_univariate(N,ff,K)
        common=euclid(pD,pN,K)
        bad=sorted(k for k,f in tests if rem(split_univariate(f,ff,K),common,K)==[])
        assert bad
        px('exact factor',n,'multiplicity',m,'excised by',bad)
    assert out is not None
    return out

def residue23(R,F,N):
    ell=23
    assert all(z%ell for z in (2,3,5,7,11,2772,sy.LC(sy.Poly(R,s))))
    f=sy.Poly(R,s,modulus=ell)
    fs=f.factor_list()[1]
    assert sorted(ff.degree()for ff,k in fs)==[1,2,14,14,14,15]
    assert all(k==1 and ff.is_irreducible for ff,k in fs)
    fac=fs[0][0].monic()
    for ff,k in fs[1:]:fac*=ff.monic()
    assert f.monic()==fac
    for poly,k in fs:
        K=FiniteExtension(poly)
        sv=K.generator
        pD=dense(D,p,K,[s],[sv]);pN=dense(N,p,K,[s],[sv])
        gg=euclid(pD,pN,K)
        assert len(gg)==2
        pv=-gg[0]
        aF=create(F.coeff(x,0),(s,p),K,(sv,pv))
        bF=create(F.coeff(x,1),(s,p),K,(sv,pv))
        assert bF!=K.zero
        ee=-aF/bF
        assert ee*bF==-aF and ee*ee-sv*ee+pv==K.zero
        A0,_,_,_,D1=base_data(sv,pv,r41,r51,K)
        # Both actual diagonal branches are excluded separately.
        assert ev(A0,ee,K)!=K.zero and D1!=K.zero
        px('prime 23 component',poly.degree(),'p,e determined; A0(e) and D1 nonzero')
    px('PASS: exceptional chart tests and rank-480 finite quotient exclusion modulo 23')

if __name__=='__main__':
    assert sy.degree(sy.gcd(J4,J5),x)==0
    slope_zero()
    F,N,R=chart(r41,r51,1)
    residue23(candidate60(N,R),F,N)

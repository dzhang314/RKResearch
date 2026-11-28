#!/usr/bin/env python3
"""Exact nonzero specialization for the (4,1,4) master norm.

This certifies a nonzero polynomial in S, not absence of tableaux.
The only tested specialization is F_19, S=7, with all guards units.
"""
import sympy as sy
from sympy.polys.agca.extensions import FiniteExtension
x,s,p,e=sy.symbols('X S P E')
J4=42*x**4-84*x**3+56*x**2-14*x+1
J5=(2*x-1)*(66*x**4-132*x**3+84*x**2-18*x+1)
G=x*(462*x**5-1260*x**4+1260*x**3-560*x**2+105*x-6)
C=x*x-s*x+p
q4,r4=sy.div(J4,C,x);q5,r5=sy.div(J5,C,x)
r40,r41=(sy.expand(r4).coeff(x,i)for i in range(2))
r50,r51=(sy.expand(r5).coeff(x,i)for i in range(2))
D=sy.Poly(r40*r51-r41*r50,s,p,domain=sy.QQ).primitive()[1].as_expr()
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

GR=sy.expand(G.subs(x,1-x))
class Unusable(ValueError):pass

class Quad:
    def __init__(self,K,S,P):
        self.K,self.S,self.P=K,S,P
        self.zero=self(K.zero)
        self.one=self(K.one)
        self.gen=self(K.zero,K.one)
    def __call__(self,v,b=None):
        if isinstance(v,X):
            assert v.F is self
            return v
        return X(self,v,self.K.zero if b is None else b)
    def convert(self,v):return self(self.K.convert(v))
    def from_sympy(self,x):return self(self.K.from_sympy(x))

class X:
    def __init__(self,F,a,b):self.F,self.a,self.b=F,a,b
    def __repr__(u):return '⟨'+str(u.a)+','+str(u.b)+'⟩'
    def __add__(u,v):
        v=u.F(v)
        return u.F(u.a+v.a,u.b+v.b)
    __radd__=__add__
    def __neg__(u):return u.F(-u.a,-u.b)
    def __sub__(u,v):return u+-u.F(v)
    def __mul__(u,v):
        v=u.F(v);t=u.b*v.b
        return u.F(u.a*v.a-u.F.P*t,u.a*v.b+u.b*v.a+u.F.S*t)
    __rmul__=__mul__
    def __pow__(u,n):
        out=u.F.one
        a=u
        while n:
            if n&1:out=out*a
            a=a*a;n//=2
        return out
    def __eq__(u,v):
        v=u.F(v)
        return u.a==v.a and u.b==v.b
    def inverse(u):
        F=u.F;n=u.a*u.a+F.S*u.a*u.b+F.P*u.b*u.b
        if n==F.K.zero:raise Unusable('nonunit in quadratic')
        vv=F((u.a+F.S*u.b)/n,-u.b/n)
        assert u*vv==F.one
        return vv
    def __truediv__(u,v):return u*u.F(v).inverse()

def mul(a,b,K):
    c=[K.zero]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b):c[i+j]+=v*w
    return trim(c,K)
def ev(a,z,K):
    out=K.zero
    for v in reversed(a):out=out*z+v
    return out
def rev(a,K):
    v=integ(a,K);w=scale(v,-K.one,K)
    return add(w,[ev(v,K.one,K)],K)
def inv_mod(a,b,K):
    assert len(b)==4 and b[-1]==K.one
    C=[rem([K.zero]*i+a,b,K)for i in range(3)]
    M=[[at(c,j,K)for j in range(3)]for c in C]
    A,B,C=M
    q=[B[1]*C[2]-B[2]*C[1],A[2]*C[1]-A[1]*C[2],A[1]*B[2]-A[2]*B[1]]
    det=q[0]*A[0]+q[1]*B[0]+q[2]*C[0]
    u=scale(q,det.inverse(),K)
    assert rem(mul(u,a,K),b,K)==[K.one]
    return u
def derivative(a,K):return trim([v*K.convert(i+1)for i,v in enumerate(a[1:])],K)

def trial(pr,n,verbose=False):
    md=sy.Poly(D.subs(s,n),p,modulus=pr)
    if md.degree()!=4 or not md.is_irreducible:return None
    V=FiniteExtension(md)
    S=V.convert(n);P=V.generator
    K=Quad(V,S,P)
    sv,pv,ee,ff=K(S),K(P),K.gen,K(S)-K.gen
    g=create(r41,(s,p),K,(sv,pv));h=create(r51,(s,p),K,(sv,pv))
    U=add(scale(dense(q5,x,K,[s,p],[sv,pv]),g,K),
          scale(dense(q4,x,K,[s,p],[sv,pv]),-h,K),K)
    assert len(U)==4 and U[-1]==K.convert(132)*g
    u=scale(U,U[-1].inverse(),K)
    one=K.one;xx=[K.zero,one]
    x1=[one,-one];C=[pv,-sv,one];xC=mul(mul(xx,x1,K),C,K)
    I0=integ([K.zero]+u,K);I1=integ([K.zero,K.zero]+u,K)
    B0=rev(mul(x1,u,K),K);B1=rev([K.zero]+mul(x1,u,K),K)
    g0=dense(G,x,K,[],[]);g1=dense(GR,x,K,[],[])
    Lv=add(I1,scale(I0,-ee,K),K)
    Rv=add(B1,scale(B0,-ff,K),K)
    ge,gf=ev(g0,ee,K),ev(g1,ff,K)
    HL=add(Lv,scale(g0,-ev(Lv,ee,K)/ge,K),K)
    HR=add(Rv,scale(g1,-ev(Rv,ff,K)/gf,K),K)
    invI,invB,invX=[inv_mod(P0,u,K)for P0 in (I0,B0,xC)]
    QA=rem(mul(HL,invI,K),u,K);QB=rem(mul(HR,invB,K),u,K)
    qL=at(QA,2,K);qR=at(QB,2,K)
    QA=scale(QA,qL.inverse(),K);QB=scale(QB,qR.inverse(),K)
    sc=[ev(integ([K.zero]*i+xC,K),one,K)for i in range(3)]
    u1,u2,u3=u[1:];m0,m1,m2=sc
    Ms=[u1*m0+u2*m1+u3*m2,u2*m0+u3*m1,u3*m0]
    M=rem(mul(mul(mul(Ms,invX,K),I0,K),B0,K),u,K)
    m2=at(M,2,K);M=scale(M,m2.inverse(),K)
    line0=add(add(add(QA,QB,K),M,K),scale(derivative(u,K),-one,K),K)
    assert len(line0)<=2
    dA=ev(I0,ee,K)/(ee*ev(u,ee,K))
    dB=ev(B0,ff,K)/((one-ff)*ev(u,ff,K))
    thetaA=-dA*dA*ee*ev(u,ee,K)/ge
    thetaB=-dB*dB*(one-ff)*ev(u,ff,K)/gf
    TA=rem(mul(g0,invI,K),u,K);TB=rem(mul(g1,invB,K),u,K)
    aa=add(TA,scale(QA,-at(TA,2,K),K),K)
    bb=add(TB,scale(QB,-at(TB,2,K),K),K)
    line1=add(add(scale(aa,thetaA,K),scale(bb,-thetaB,K),K),[sv-dB+dA,-K.convert(2)],K)
    assert len(line1)<=2
    determinant=at(line0,0,K)*at(line1,1,K)-at(line0,1,K)*at(line1,0,K)
    determinant.inverse()
    if verbose:
        print('prime',pr,'S=',n,'irreducible D in P:',md.monic().as_expr())
        print('Both line coefficient lists:',line0,line1)
        print('nonzero line determinant norm:',determinant.a*determinant.a+S*determinant.a*determinant.b+P*determinant.b*determinant.b)
    return True

if __name__=='__main__':
    assert trial(19,7,True)
    print('PASS: all denominator/leading guards and the affine-line determinant are units in the rank-eight specialization')

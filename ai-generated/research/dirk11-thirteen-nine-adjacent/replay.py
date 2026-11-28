#!/usr/bin/env python3
"""Exact nine-label adjacent-face elimination for normalized DIRK11/13.

SymPy provides rational polynomial division/resultants. The finite field
part performs polynomial remainders explicitly and only needs a good
reduction of one *finite free* rational quotient. No floating point.
"""
import sympy as sy
from sympy.polys.agca.extensions import FiniteExtension
from pathlib import Path
x,s,p,e=sy.symbols('X S P E')
J4=42*x**4-84*x**3+56*x**2-14*x+1
J5=(2*x-1)*(66*x**4-132*x**3+84*x**2-18*x+1)
G=x*(462*x**5-1260*x**4+1260*x**3-560*x**2+105*x-6)
C=x*x-s*x+p
q4,r4=sy.div(J4,C,x);q5,r5=sy.div(J5,C,x)
r40,r41=(sy.expand(r4).coeff(x,i)for i in range(2))
r50,r51=(sy.expand(r5).coeff(x,i)for i in range(2))
D=sy.Poly(r40*r51-r41*r50,s,p,domain=sy.QQ).primitive()[1].as_expr()
def red(A,d=C):
    return sy.rem(sy.expand(A),d,x)
def inte(A):
    q=sy.Poly(A,x)
    return sum(co/(k[0]+1)*x**(k[0]+1)for k,co in q.terms())
def at1(A):return A.subs(x,1)
def ordinary(A):return at1(inte(A))
def calc(d,j):
    # The scaled U here is exactly d times U on the chart d!=0.
    U=sy.expand(d*q5-j*q4)
    A=inte(x*U)
    B=inte((1-x)*U)
    B=at1(B)-B
    AB=sy.expand(A*B)
    F,r=sy.div(AB,x*(1-x),x)
    assert not r
    F=red(F)
    Urem=red(U)
    Uconj=sy.expand(Urem.subs(x,s-x))
    norm=red(Urem*Uconj)
    assert not norm.has(x)
    v0=ordinary(x*(1-x)*U)
    v1=ordinary(x*x*(1-x)*U)
    T=red(F*Uconj*(v1-v0*(s-x)))
    # Mixed condition is S0=0; multiplied by the nonzero norm U(e)U(f).
    S0=sy.expand(ordinary(AB)*norm-T.coeff(x,1))
    return S0


def primitiveZZ(f,vs):
    return sy.Poly(f,*vs,domain=sy.QQ).clear_denoms()[1].primitive()[1].as_expr()

def mixed(c,d):
    value=calc(c,d)
    return primitiveZZ(sy.reduced(value,[D],s,p)[1],(s,p))

S1=mixed(r41,r51)
S0=mixed(r40,r50)
R1=sy.resultant(D,S1,p)
R0=sy.resultant(D,S0,p)
rguard=sy.resultant(D,r41,p)
assert sy.Poly(sy.gcd(R0,rguard),s).degree()==0
print('exact zero-slope chart: two resultants coprime')
L0=s-1
L4=99*s**4-396*s**3+573*s**2-354*s+79
R,left=sy.div(R1,L0**8*L4**4,s)
assert left==0
R=primitiveZZ(R,(s,))
assert sy.degree(R,s)==36
assert r41.subs(s,1)==0
# Work in the exact formal algebra QQ[S]/L4. Every quotient operation
# used by the explicit Euclidean algorithm below verifies an actual inverse.
K4=sy.QQ.algebraic_field((sy.Poly(L4,s),s))
def rational_extension(p0,field):
    cf=sy.Poly(sy.rem(p0,L4,s),s,domain=sy.QQ).all_coeffs()
    return field([sy.QQ.convert(c)for c in cf])

def exact_L4_gate():
    convert=lambda expr:[rational_extension(sy.Poly(expr,p).nth(i),K4)
                          for i in range(sy.degree(expr,p)+1)]
    gg=euclid(convert(D),convert(S1),K4)
    assert len(gg)==2
    assert rem(convert(r41),gg,K4)==[]
    print('exact slope denominators: S=1 and L4 force the forbidden zero slope')

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

def px(*m):print(*m,flush=True)

def test(pr,verbose=False):
    if any(a%pr==0 for a in (2,3,5,7,11,2772,sy.LC(sy.Poly(R,s)))):return False
    FF=sy.Poly(R,s,modulus=pr)
    fs=FF.factor_list()[1]
    assert [f.degree()for f,k in fs]==[2,34]
    assert all(k==1 and f.is_irreducible for f,k in fs)
    assert FF.monic()==fs[0][0].monic()*fs[1][0].monic()
    px('prime',pr,'squarefree factor degrees',[f.degree()for f,k in fs])
    seen=[]
    for ff,k in fs:
        K=FiniteExtension(ff); sv=K.generator
        Dc=dense(D,p,K,[s],[sv]);Sc=dense(S1,p,K,[s],[sv])
        g=euclid(Dc,Sc,K)
        assert len(g)==2
        pv=-g[0]
        da=create(r41,(s,p),K,(sv,pv))
        assert da!=K.zero
        va=create(r51,(s,p),K,(sv,pv))
        U=add(scale(dense(q5,x,K,[s,p],[sv,pv]),da,K),
              scale(dense(q4,x,K,[s,p],[sv,pv]),-va,K),K)
        assert len(U)==4
        A0=integ([K.zero]+U,K)
        A1=integ([K.zero,K.zero]+U,K)
        GG=dense(G,x,K,[],[])
        def add2(z,w):return z[0]+w[0],z[1]+w[1]
        def neg2(z):return -z[0],-z[1]
        def mul2(z,w):
            a,b=z;c,d=w;t=b*d
            return a*c-pv*t,a*d+b*c+sv*t
        def to2(t):return t,K.zero
        zz=(K.zero,K.one)
        def eval2(p):
            v=(K.zero,K.zero)
            for a in reversed(p):v=add2(mul2(v,zz),to2(a))
            return v
        a0e=eval2(A0);a1e=eval2(A1);ge=eval2(GG)
        a0r=rem(A0,U,K);a1r=rem(A1,U,K)
        x0r=rem([K.zero]+A0,U,K);gr=rem(GG,U,K)
        v0=[to2(at(a0r,i,K)) for i in range(3)]
        v1=[to2(at(x0r,i,K)) for i in range(3)]
        qv=[add2(mul2(ge,add2(to2(at(a1r,i,K)),neg2(mul2(zz,v0[i])))),
                 neg2(mul2(add2(a1e,neg2(mul2(zz,a0e))),to2(at(gr,i,K)))))for i in range(3)]
        # Determinant of the three remainder columns in basis 1,X,X².
        det=(K.zero,K.zero)
        for i,j,k,sgn in ((0,1,2,1),(1,2,0,1),(2,0,1,1),(0,2,1,-1),(2,1,0,-1),(1,0,2,-1)):
            v=mul2(v0[i],mul2(v1[j],qv[k]));det=add2(det,v if sgn==1 else neg2(v))
        a,b=det
        norm=a*a+sv*a*b+pv*b*b
        assert norm!=K.zero
        seen.append((ff.degree(),'linear p; unit affine norm'))
        px('successful factor',seen[-1])
    px('PASS: finite quotient generator ideal has full rank',2*4*36,'modulo',pr)
    return True


if __name__=='__main__':
    exact_L4_gate()
    assert test(19)

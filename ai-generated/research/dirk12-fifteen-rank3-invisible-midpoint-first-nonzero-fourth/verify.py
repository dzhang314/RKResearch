#!/usr/bin/env python3
"""Exact number-field replay: midpoint first live clock, nonzero fourth diagonal."""
from fractions import Fraction
from math import comb
import sympy as S
from sympy import QQ


def poly_add(u,v):
    w=[0]*max(len(u),len(v))
    for i,c in enumerate(u):w[i]+=c
    for i,c in enumerate(v):w[i]+=c
    return trim(w)


def trim(u):
    while u and not u[-1]:u.pop()
    return u


def scl(u,v):
    return trim([v*c for c in u])


def sub(u,v):return poly_add(u,scl(v,-1))


def mul(u,v):
    if not u or not v:return []
    w=[0]*(len(u)+len(v)-1)
    for i,c in enumerate(u):
        for j,d in enumerate(v):w[i+j]+=c*d
    return trim(w)


def hull(F,nodes):
    ans=[F(1)]
    for x in nodes:ans=mul(ans,[-x,F(1)])
    return ans


def ev(u,x):
    z=0
    for i in reversed(u):z=z*x+i
    return z


def integ(F,p):return [F(0)]+[c/F(i+1) for i,c in enumerate(p)]


def leg(F,n,a):
    return [F(k*(-1)**(n-k)*comb(n,k)*comb(n+k,k))*a**(k-1) for k in range(1,n+1)]


def exactquot(F,a,b):
    d=list(a); o=[F(0)]*(len(a)-len(b)+1)
    while d and len(d)>=len(b):
        i=len(d)-len(b); c=d[-1]/b[-1]
        o[i]=c; d=sub(d,[F(0)]*i+scl(b,c))
    assert not d
    return trim(o)


def solve(M,B):
    u=[list(r)+[c] for r,c in zip(M,B)]
    for i in range(len(u)):
        j=next(j for j in range(i,len(u)) if u[j][i])
        u[j],u[i]=u[i],u[j]
        fact=u[i][i]
        u[i]=[c/fact for c in u[i]]
        for j in range(len(u)):
            if j==i:continue
            fact=u[j][i]
            u[j]=[c-fact*d for c,d in zip(u[j],u[i])]
    return [r[-1] for r in u]


class Quadratic:
    def __init__(self,K,q0,q1):
        self.K=K;self.q0=q0;self.q1=q1
    def __call__(self,v):
        if isinstance(v,E):
            assert v.F is self
            return v
        if isinstance(v,tuple):return E(self,self.K.convert(v[0]),self.K.convert(v[1]))
        if isinstance(v,Fraction):v=S.Rational(v.numerator,v.denominator)
        return E(self,self.K.convert(v),self.K.zero)


class E:
    def __init__(self,F,a,b):
        self.F,self.a,self.b=F,a,b
    def __bool__(self):return bool(self.a) or bool(self.b)
    def __eq__(self,v):
        v=self.F(v)
        return self.a==v.a and self.b==v.b
    def __neg__(self):return E(self.F,-self.a,-self.b)
    def __add__(self,v):
        v=self.F(v)
        return E(self.F,self.a+v.a,self.b+v.b)
    __radd__=__add__
    def __sub__(self,v):return self+-self.F(v)
    def __rsub__(self,v):return self.F(v)+-self
    def __mul__(self,v):
        v=self.F(v); p=self.b*v.b
        return E(self.F,self.a*v.a-self.F.q0*p,
                 self.a*v.b+self.b*v.a-self.F.q1*p)
    __rmul__=__mul__
    def __pow__(self,n):
        v=self.F(1)
        for _ in range(n):v*=self
        return v
    def inv(self):
        c=self.a-self.b*self.F.q1
        n=self.a*c+self.b*self.b*self.F.q0
        assert n
        return E(self.F,c/n,-self.b/n)
    def __truediv__(self,v):return self*self.F(v).inv()
    def __rtruediv__(self,v):return self.F(v)*self.inv()


def main():
    T,x,y,t=S.symbols('T x y t')
    a=S.Rational(1,2)
    L=S.diff(S.legendre(6,2*T-1),T)
    ell=lambda v:L.subs(T,a*v)
    J=lambda p:S.integrate(S.expand(p),T)
    P0=T*(T-1)*(T-x)*(T-y)
    I0=J(P0).subs(T,1); I1=J(T*P0).subs(T,1)
    tr=S.cancel(I1/I0)
    n,d=tr.as_numer_denom()
    Db=5*x*x-5*x+1
    kb=-30*x**3*(x-1)**3/Db
    eps=-(7*x*x-7*x+2)/1260
    K=P0*(T-t)
    raw=J(K).subs(T,t)*x*ell(x)-kb*t*ell(t)*(J(T*K).subs(T,1)-eps)
    nr=S.factor(raw.subs(t,tr)).as_numer_denom()[0]
    H=S.cancel(nr/(x*(x-1)*n*(n-d)*(n-x*d)))
    assert S.Poly(H,x,y).degree_list()==(8,5)
    H=S.Poly(H,x,y).primitive()[1].clear_denoms(convert=True)[1].as_expr()
    D=2*x*y-x-3*y*y+2*y;M=3*x*x-2*x*y-2*x+y
    Y0=x*x*(x-1)**3*D*ell(y)+y*y*(y-1)**3*M*ell(x)
    Y=S.cancel(Y0/((x-1)*(y-1)*(x-y)))
    assert S.Poly(Y,x,y).degree_list()==(5,5)
    Y=S.Poly(Y,x,y).primitive()[1].clear_denoms(convert=True)[1].as_expr()
    R=S.Poly(S.resultant(Y,H,y),x)
    fs=S.factor_list(R)[1]
    assert [(f.degree(),e) for f,e in fs]==[(2,4),(4,2),(13,1),(18,2)]
    assert S.cancel(fs[0][0].as_expr()/Db).is_constant()
    assert S.cancel(fs[1][0].as_expr()*(x-1)/ell(x)).is_constant()
    print('actual first-root t and third equations: exact outer factor degrees 2,4,13,18')

    def fieldlift(p):
        F=QQ.alg_field_from_poly(p,alias='xi')
        R=F.poly_ring(y).ring
        xx=F.unit
        def ins(f):
            out={}
            for (i,j),c in S.Poly(f,x,y).terms():
                out[(j,)]=out.get((j,),F.zero)+F.convert(c)*xx**i
            return R.from_dict(out)
        return F,xx,ins(Y).gcd(ins(H)).monic()

    V,bx,G=fieldlift(fs[2][0])
    assert G.degree()==1
    by=-G[(0,)]
    # The genuine I1-yI0 test, not a mere modular coincidence.
    def ins2(f,F,a,b):
        return sum(F.convert(c)*a**i*b**j for (i,j),c in S.Poly(f,x,y).terms())
    assert ins2(I0,V,bx,by) and not ins2(I1-y*I0,V,bx,by)
    print('degree-13 factor: every exact third root repeats at the fourth row')

    F,bx,G=fieldlift(fs[3][0])
    assert G.degree()==2
    A=Quadratic(F,G[(0,)],G[(1,)])
    x0,y0=A(bx),A((0,1))
    z,o,h=A(0),A(1),A(a)
    P0=hull(A,[z,o,x0,y0])
    i0=ev(integ(A,P0),o);i1=ev(integ(A,[z]+P0),o)
    t=i1/i0
    (t*(t-o)*(t-x0)*(t-y0)).inv()
    K=mul(P0,hull(A,[t]))
    modes=[[z]+leg(A,j,h) for j in (5,6,7)]
    M=[[ev(L,clock) for L in modes] for clock in (o,x0,y0)]
    def actual(p):
        root=integ(A,p)
        cs=solve(M,[ev(root,clock) for clock in (o,x0,y0)])
        for L,c in zip(modes,cs):root=sub(root,scl(L,c))
        return root
    v=actual(K);w=actual([z]+K)
    assert not ev(v,t) and not ev(w,t)
    c=exactquot(A,sub(w,[z]+v),K)
    assert len(c)==3 and c[1]*c[1]==4*c[0]*c[2]
    f=-c[1]/(2*c[2])
    assert not ev(c,f)
    print('degree-18 factor with quadratic y: exact repeated-root fifth polynomial')

    labels=[z,o]+[o-h*s for s in (o,x0,y0,t,f)]
    for i,q in enumerate(labels):
        for j in labels[:i]:(q-j).inv()
    P=hull(A,labels)
    m=[ev(integ(A,[z]*j+P),o) for j in range(5)]
    for M0 in m[:4]:M0.inv()
    q=m[0]*m[2]/(m[1]*m[1]);H=3*m[1]/(2*m[0])
    L=4*q/(9-4*q)
    sm=H*L; pr=H*H*L*L/(L+4); u=-H*L/(L-2)
    w=1-h*f
    assert not (w-u)*(w*w-sm*w+pr)
    print('exact reconstructed reverse cubic contains the already fixed fifth live label')


if __name__=='__main__':
    main()

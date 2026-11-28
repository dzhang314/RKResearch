"""Exact degree-66 projection for actual ordinary hole six, star cubic fifth."""
from functools import lru_cache
from sympy import Poly, QQ, Rational, symbols, sqrt
from flint import fmpq, fmpq_mpoly_ctx, fmpq_poly

X,R,G=symbols("X r gamma")


def P(v):
    return Poly(v,X,R,G,domain=QQ)


def integral(f):
    terms={}
    for (i,j,k),a in f.rep.to_dict().items():
        m=(0,j,k)
        terms[m]=terms.get(m,QQ(0))+a/QQ(i+1)
    return Poly.from_dict(terms,X,R,G,domain=QQ)


def literal_D():
    d2=(1680*G**4-840*G**3+180*G**2-20*G+1)/4
    d1=-1680*G**4+1050*G**3-270*G**2+35*G-2
    d0=(2520*G**4-1680*G**3+540*G**2-120*G+11)/4
    a,b=2+sqrt(2),2-sqrt(2)
    L4=lambda y:70*y**4-140*y**3+90*y**2-20*y+1
    h4=Rational(3,4)-9*X/4+9*X**2/8-X**3/8
    ell=(L4(G*a)*(b-X)/((a-1)/2)+L4(G*b)*(X-a)/((b-1)/2))/(b-a)
    rhs=L4(G*X)-ell*h4
    expect=(X-a)*(X-b)*(d2*X**2+d1*X+d0)
    assert Poly(rhs-expect,X,G,domain=QQ.algebraic_field(sqrt(2))).is_zero
    return tuple(map(P,(d0,d1,d2)))


@lru_cache(None)
def fields():
    d0,d1,d2=literal_D()
    J=P(R**4-16*G*R**3+72*G**2*R**2-96*G**3*R+24*G**4)
    Lr=P(70*R**4-140*R**3+90*R**2-20*R+1)
    E2=P(X**2-4*G*X+2*G**2)
    E4=E2*(d2*J*P(X**2)+d1*J*P(G*X)+(d0*J+9*P(G**4)*Lr)*P(G**2))
    H4=P(6*G**3-18*G**2*X+9*G*X**2-X**3)
    F=[integral(P((X-R)*X**j)*H4) for j in range(3)]
    E=[integral(P((X-R)*X**j)*E4) for j in range(3)]
    return F,E,(d0,d1,d2,J,Lr),H4,E4


C=fmpq_mpoly_ctx.get(("r","gamma"),ordering="lex")


def cv(v):
    return C.from_dict({(i,j):fmpq(str(a))
                        for (i,j),a in Poly(v.as_expr(),R,G,domain=QQ).terms()})


def row(a,k):
    return fmpq_poly([a.get((k,j),0)
                      for j in range(max((i[1] for i in a),default=0)+1)])


def trim(v):
    while v and not v[-1]:
        v.pop()
    return v


def qmon(v):
    return v/v.leading_coefficient()


def exact_fiber_gcd(polys,M):
    """Polynomial in r over the exact number field Q[gamma]/M."""
    def inv(v):
        d,a,_=v.xgcd(M)
        assert d==fmpq_poly([1])
        return a

    def rem(a,b):
        a=a[:]
        invlc=inv(b[-1])
        while len(a)>=len(b):
            h=(a[-1]*invlc)%M
            off=len(a)-len(b)
            for i,c in enumerate(b):
                a[off+i]=(a[off+i]-h*c)%M
            trim(a)
        return a

    def unif(q):
        a=q.to_dict()
        return trim([row(a,k)%M for k in range(q.degrees()[0]+1)])

    def gcd(a,b):
        while b:
            a,b=b,rem(a,b)
        if not a:
            return []
        d=inv(a[-1])
        return [(x*d)%M for x in a]

    d=[]
    for q in polys:
        d=gcd(d,unif(q))
    return d,rem,unif


@lru_cache(None)
def model():
    F,E,guard,H4,E4=fields()
    F,E=[list(map(cv,ts)) for ts in (F,E)]
    pairs=((0,1),(0,2),(1,2))
    B=[F[i]*E[j]-F[j]*E[i] for i,j in pairs]
    assert [v.degrees() for v in B]==[(6,14)]*3
    rF=[F[i].resultant(F[j],0) for i,j in pairs]
    assert all(v.degrees()==(0,6) for v in rF)
    one=rF[0].gcd(rF[1]).gcd(rF[2])
    assert one.degrees()==(0,0) and one!=0
    rB=[B[i].resultant(B[j],0) for i,j in pairs]
    assert [v.degrees() for v in rB]==[(0,148)]*3
    m=qmon(row(rB[0].gcd(rB[1]).gcd(rB[2]).to_dict(),0))
    factors=m.factor()[1]
    assert sorted((q.degree(),i) for q,i in factors)==[(1,24),(4,4),(16,1),(66,1)]
    prod=fmpq_poly([1])
    M={}
    for q,i in factors:
        q=qmon(q)
        M[q.degree()]=q
        prod*=q**i
    assert prod==m and M[1]==fmpq_poly([0,1])

    # No p-local approximation in either exceptional gamma component.
    Lr=cv(guard[-1])
    d,_,u=exact_fiber_gcd(B,M[4])
    l=u(Lr)
    assert len(d)==5 and d==[a/70 for a in l]
    d,rem,u=exact_fiber_gcd(B,M[16])
    assert len(d)==2 and all(not rem(u(e),d) for e in E)
    print("exact degree-148 projections; remove gamma, exact degree-4 Gauss",
          "and degree-16 rank-loss fibers; retain complete degree 66",flush=True)
    return F,E,B,M[66],tuple(map(cv,guard)),[cv(Poly(H4.as_expr(),X).nth(i)) for i in range(4)],[
        cv(Poly(E4.as_expr(),X).nth(i)) for i in range(5)]


if __name__=="__main__":
    model()

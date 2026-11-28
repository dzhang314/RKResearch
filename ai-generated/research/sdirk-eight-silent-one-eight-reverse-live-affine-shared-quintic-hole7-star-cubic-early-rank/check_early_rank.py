"""Full early-anchor rank loss for corrected cubic-fifth actual hole seven."""
from sympy import QQ, Poly, Rational, sqrt, symbols
from flint import fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx,nmod_poly
from itertools import combinations

X,R,G=symbols("X r gamma")
L=[1,2*X-1,6*X**2-6*X+1,20*X**3-30*X**2+12*X-1,
   70*X**4-140*X**3+90*X**2-20*X+1]
PI=1400*G**4-840*G**3+180*G**2-20*G+1


def slopes():
    K3=sum((2*j+1)*L[j]*Poly(L[j],X).eval(R) for j in range(4))
    a,b=2+sqrt(2),2-sqrt(2)
    Q=QQ.algebraic_field(sqrt(2))
    def read(F):
        fa=F.subs(X,a*G)/((a-1)/2)
        fb=F.subs(X,b*G)/((b-1)/2)
        m=Poly((fb-fa)/(b-a),R,G,domain=Q)
        assert all(len(v.to_list())==1 for v in m.rep.to_dict().values())
        return Poly(m.as_expr(),R,G,domain=QQ)
    l,k=map(read,(L[4],K3))
    assert l==Poly(2*PI,R,G,domain=QQ) and k.degree(R)==3
    d0=(2520*G**4-1680*G**3+540*G**2-120*G+11)/4
    ell0=Rational(4,3)*(1-2*d0)
    assert Poly(ell0,G,domain=QQ).gcd(Poly(PI,G,domain=QQ))==1
    return k


def check():
    K3=slopes()
    p=1009
    pi=nmod_poly([1,-20,180,-840,1400],p)*pow(1400,-1,p)
    assert pi.degree()==4 and pi.factor()[1]==[(pi,1)]
    K=fq_default_ctx(modulus=fmpz_mod_poly_ctx(p)([int(a) for a in pi.coeffs()]),var="g")
    W=fq_default_poly_ctx(K)
    r=W.gen()
    g=K.gen()
    aa=[K(0)]*4
    for (i,j),v in K3.terms():
        aa[i]+=int(v.p)*pow(int(v.q),-1,p)%p*g**j
    P=W(aa)
    assert P.degree()==3
    q=P/P.leading_coefficient()
    assert q.factor()[1]==[(q,1)]
    d2=(1680*g**4-840*g**3+180*g**2-20*g+1)/4
    d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
    d0=(2520*g**4-1680*g**3+540*g**2-120*g+11)/4
    assert g!=0 and d2!=0 and 4*(1-2*d0)/3!=0
    E2=r*r-4*g*r+2*g*g
    L0=E2*(d2*r*r+g*d1*r)
    def I(P,k):
        return sum(P[i]/(i+k+1) for i in range(P.degree()+1))
    cols=[[I(P,j+1)-r*I(P,j) for P in (L0,E2)] for j in range(3)]
    D=[cols[i][0]*cols[j][1]-cols[i][1]*cols[j][0]
       for i,j in combinations(range(3),2)]
    assert all(x.degree()<=2 for x in D)
    h=q
    for x in D:
        h=h.gcd(x)
    assert h==1
    print("early rank: complete gamma4/r3 tower, paid two-column moment rank 2 at every root")


if __name__=="__main__":
    check()

"""Exact slope-zero diagonal and complete local arithmetic for the actual sixth hole."""
from sympy import Poly, QQ, Rational, expand, symbols
from flint import fq_default_ctx, fq_default_poly_ctx, fmpz_mod_poly_ctx, nmod_poly
from itertools import combinations

R12=[17,-825,20170,-320520,3616560,-30205800,190510800,-912794400,3303417600,
     -8812944000,16130016000,-16595712000,4741632000]


def coefficients(g):
    d2=(1680*g**4-840*g**3+180*g**2-20*g+1)/4
    d1=-1680*g**4+1050*g**3-270*g**2+35*g-2
    d0=(2520*g**4-1680*g**3+540*g**2-120*g+11)/4
    return d0,d1,d2


def exact_diagonal():
    g,s,R,h,D,L=symbols("gamma s R eta D L")
    d0,d1,d2=coefficients(g)
    assert Poly(d1,g,domain=QQ).gcd(Poly(d2,g,domain=QQ))==Poly(1,g,domain=QQ)
    y=(3*s-1)/2
    ell=(1-2*d0)*Rational(4,3)+8*(d2-70*g**4)*y
    D0=d2*s*s+d1*s+d0
    U=Poly(ell+Rational(4,3)*D0*(5-s),s)
    assert U.degree()==3
    proj=sum(U.nth(i)*(d2-2*d1)**i*(5*d2)**(3-i) for i in range(4))
    assert Poly(3*proj-d2*sum(R12[i]*g**i for i in range(13)),g,domain=QQ).is_zero

    # Audit the unnormalized actual sixth identity, including both zero slopes.
    w0,w1,w2=R-1,R*R/2-R,R**3/3-R*R
    w3base=R**4/4-R**3
    wd=[D*w0,D*w1,D*w2,D*w3base+L/4]
    H=[Rational(3,4),-Rational(9,4),Rational(9,8),-Rational(1,8)]
    E=[-2*s,4*s+2,-s-4,1]
    def read(c):
        return sum(a*b for a,b in zip(c,wd))
    J=R**4-16*R**3+72*R*R-96*R+24
    M=w3base-(s+4)*w2+(4*s+2)*w1-2*s*w0
    assert expand(32*(L/4-read(H)-h*read(E))-((9-8*h)*L+D*(J-32*h*M)))==0


def det(M):
    a,b,c=M
    return sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3])
               for i in range(3))


def full_fiber():
    p=1009
    m=nmod_poly(R12,p)*pow(R12[-1],-1,p)
    assert m.degree()==12 and m.leading_coefficient()==1
    fac=m.factor()[1]
    assert len(fac)==1 and fac[0]==(m,1)
    K=fq_default_ctx(modulus=fmpz_mod_poly_ctx(p)([int(a) for a in m.coeffs()]),
                     var="g")
    W=fq_default_poly_ctx(K)
    r=W.gen()
    g=K.gen()
    d0,d1,d2=coefficients(g)
    assert g!=0 and d2!=0
    s=(d2-2*d1)/(5*d2)
    y=(3*s-1)/2
    D=d2*s*s+d1*s+d0
    assert D!=0
    c3=W([6*g**3,-18*g*g,9*g,-1])
    e3=W([2*g*g,-4*g,1])*W([-s*g,1])
    e4=e3*W([-y*g,1])

    def mm(h,j):
        return sum(h[i]/(i+j+1) for i in range(h.degree()+1))

    rows=[[mm(h,j+1)-mm(h,j)*r for h in (c3,8*e3,e4)] for j in range(3)]
    L=70*r**4-140*r**3+90*r*r-20*r+1
    J=r**4-16*g*r**3+72*g*g*r*r-96*g**3*r+24*g**4
    M=(r**4/4-g*r**3-(s+4)*(g*r**3/3-g*g*r*r)
       +(4*s+2)*(g*g*r*r/2-g**3*r)-2*s*(g**3*r-g**4))
    sixth=[9*g**4*L+D*J,-8*g**4*L-32*D*M,W(0)]
    cuts=[det(rows),*[det([rows[i],rows[j],sixth]) for i,j in combinations(range(3),2)]]
    assert [c.degree() for c in cuts]==[3,6,6,6]
    common=cuts[0]
    for c in cuts[1:]:
        common=common.gcd(c)
    assert common==1
    print("complete exact degree-12 fifth zero-pivot diagonal; p=1009:",
          "full r degrees 3,6,6,6 and common gcd 1",flush=True)


if __name__=="__main__":
    exact_diagonal()
    full_fiber()

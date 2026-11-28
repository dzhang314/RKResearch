"""Prove the regular exceptional star-front scalar projection is finite."""
from flint import fmpq_mpoly_ctx,fmpq,fmpq_poly,nmod_poly
from itertools import combinations

C=fmpq_mpoly_ctx.get(("r","s","gamma"),ordering="lex")
r,s,g=C.gens()


def mul(a,b):
    z=[C.constant(0)]*(len(a)+len(b)-1)
    for i,a0 in enumerate(a):
        for j,b0 in enumerate(b):
            z[i+j]+=a0*b0
    return z


def model():
    d2=(1680*g**4-840*g**3+180*g*g-20*g+1)/4
    d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
    d0=(2520*g**4-1680*g**3+540*g*g-120*g+11)/4
    D=d2*s*s+d1*s+d0
    y=(3*s-1)/2
    U=(1-2*d0)*fmpq(4,3)+8*(d2-70*g**4)*y+fmpq(4,3)*D*(5-s)
    V=d2*(y+s)+d1
    E3=mul([2*g*g,-4*g,C.constant(1)],[-s*g,C.constant(1)])
    F=[U*a+8*V*b for a,b in zip([6*g**3,-18*g*g,9*g,C.constant(-1)],E3)]
    E=mul(E3,[-y*g,C.constant(1)])

    def moment(q,j):
        return sum(c/(i+j+1) for i,c in enumerate(q))

    def row(q):
        return [moment(q,j+1)-r*moment(q,j) for j in range(3)]

    f,e=row(F),row(E)
    B=[f[i]*e[j]-f[j]*e[i] for i,j in combinations(range(3),2)]
    L=70*r**4-140*r**3+90*r*r-20*r+1
    G=r**4-16*g*r**3+72*g*g*r*r-96*g**3*r+24*g**4
    M=(r**4/4-g*r**3-(s+4)*(g*r**3/3-g*g*r*r)
       +(4*s+2)*(g*g*r*r/2-g**3*r)-2*s*(g**3*r-g**4))
    T=(9*U-8*V)*g**4*L+D*(U*G-32*V*M)
    return B,T


def main():
    B,T=model()
    assert [b.degrees() for b in B]==[(2,5,10)]*3 and T.degrees()==(4,5,12)

    def cr(p,k):
        return C.from_dict({(0,j,l):a for (i,j,l),a in p.to_dict().items() if i==k})

    b=[[cr(h,k) for k in range(3)] for h in B]
    S=sum(b[0][k]*(b[1][(k+1)%3]*b[2][(k+2)%3]
                   -b[1][(k+2)%3]*b[2][(k+1)%3]) for k in range(3))
    A=B[0].resultant(T,0)
    assert S.degrees()==(0,15,30) and A.degrees()==(0,30,64)
    def cs(q,j):
        z=q.to_dict()
        return fmpq_poly([z.get((0,j,k),0) for k in range(q.degrees()[2]+1)])
    content=cs(S,0)
    for j in range(1,16):
        content=content.gcd(cs(S,j))
    assert content==1
    # This specialization proves that the true outer polynomial is nonzero;
    # it is deliberately not a test of solutions at all other diagonals.
    p=1009
    def specialize(H):
        ds=[cs(H,j)(1) for j in range(H.degrees()[1]+1)]
        return nmod_poly([int(c.p)*pow(int(c.q),-1,p)%p for c in ds],p)
    a,b=map(specialize,(S,A))
    assert (a.degree(),b.degree())==(15,30) and a.gcd(b)==1
    print("Q-exact finite projection: s degrees 15 and 30, full nonzero resultant;",
          "primitive moment determinant in gamma; no fiber exclusion claimed",flush=True)


if __name__=="__main__":
    main()

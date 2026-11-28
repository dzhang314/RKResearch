"""Complete standalone regular-rank, nonzero-sixth-slope star cubic seventh proof."""
from compact_cubic import generic, star, arithmetic, silent8
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx,fmpz_mod_poly_ctx

P=1009


def reduce_coeff(x):
    return int(x.p)*pow(int(x.q),-1,P)%P


def physical_r(q,g,B,W):
    out=[B(0)]*(q.degrees()[1]+1)
    for (i,j,k),a in q.to_dict().items():
        assert i==0
        out[j]+=reduce_coeff(a)*g**k
    return W(out)


def physical_c(q,r,g,B,W):
    out=[B(0)]*(q.degrees()[0]+1)
    for (i,j,k),a in q.to_dict().items():
        out[i]+=reduce_coeff(a)*r**j*g**k
    return W(out)


def silent8_check():
    m,S,A,B=silent8()
    d=nmod_poly([reduce_coeff(x) for x in m.coeffs()],P)
    assert d.degree()==54 and d.leading_coefficient()==1
    parts=d.factor()[1]
    assert sorted((z.degree(),e) for z,e in parts)==[
        (2,1),(3,1),(4,1),(4,1),(8,1),(33,1)]
    prod=nmod_poly([1],P)
    for a,e in parts:
        prod*=a**e
    assert prod==d
    H,E2,abc,W0,W1,_,gs=generic()
    cnt=0
    for a,e in parts:
        K=fq_default_ctx(modulus=fmpz_mod_poly_ctx(P)(
            [int(x) for x in a.coeffs()]),var="g")
        g=K.gen()
        W=fq_default_poly_ctx(K)
        t=W.gen()
        R=[physical_r(q,g,K,W) for q in [S,*A]]
        assert [z.degree() for z in R]==[3,20,23,23]
        T=R[0]
        for h in R[1:]:
            T=T.gcd(h)
        assert T.degree()==1
        r=-T[0]/T[1]
        U=[physical_c(q,r,g,K,W) for q in B]
        assert [x.degree() for x in U]==[1,1,1]
        S0=U[0].gcd(U[1]).gcd(U[2])
        assert S0.degree()==1
        c=-S0[0]/S0[1]
        read=lambda q:physical_r(q,g,K,W)(r)
        assert g!=0 and read(W1)!=0
        HH=W([read(h) for h in H])
        assert HH.degree()==4
        hh=HH/HH.leading_coefficient()
        # H(r) vanishes in these residue fibers, not an eliminated source guard.
        assert hh(r)==0
        x=1-g
        u=(x-c)/g
        k=1+2*t-t*t
        F=(t-2)*hh(x-g*t)-(2*t+k*(t-2))*hh(x)
        Ft,rem=divmod(F,t)
        assert rem.is_zero() and Ft.degree()==4 and Ft.leading_coefficient()==g**4
        N=W([read(j) for j in E2])*W([read(j) for j in abc])*W([read(W0),read(W1)])
        terminal=hh(c)*N(c)+hh(x)*N(x)
        assert Ft(u)!=0 and terminal!=0
        cnt+=1
    assert cnt==6
    print("actual silent eighth: p=1009, all six gamma54 components;",
          "full r/c degrees, actual rear and terminal both exclude",flush=True)


if __name__=="__main__":
    star()
    arithmetic()
    silent8_check()

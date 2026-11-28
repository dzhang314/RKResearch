"""Complete exceptional regular star-rear exclusion, source-guarded residue tests."""
from compact_star_head import diag,cuts,small_exact_guard,reduce_coef
from flint import (fmpq_poly,nmod_poly,nmod_mpoly_ctx,fmpz_mod_poly_ctx,
                   fq_default_ctx,fq_default_poly_ctx)
from collections import Counter

P=1009
GUARDS={(12,1):(2,1),(12,3):(2,1),(3,2):(2,1),(4,6):(2,3),
        (30,2):(1,1),(42,1):(7,1)}


def modpoly(f):
    p=nmod_poly([reduce_coef(x,P) for x in f.coeffs()],P)
    assert p.degree()==f.degree() and p.leading_coefficient()==1
    return p


def factors(f):
    z=f**0
    out=f.factor()[1]
    for u,j in out:z*=u**j
    assert z==f
    return out


def auxiliary(K,T):
    C=nmod_mpoly_ctx.get(("q","r","gamma"),P)
    cv=lambda f:C.from_dict({m:reduce_coef(v,P) for m,v in f.to_dict().items()})
    A,B=cv(K),cv(T)
    assert A.degrees()==K.degrees() and B.degrees()==T.degrees()
    R=A.resultant(B,1)
    tab=R.to_dict()
    assert R.degrees()[:2]==(0,0)
    return nmod_poly([int(tab.get((0,0,j),0)) for j in range(R.degrees()[2]+1)],P)


def effective_degree(q,f):
    a=q.to_dict()
    return max(i for i in range(q.degrees()[1]+1)
               if fmpq_poly([a.get((0,i,j),0) for j in range(q.degrees()[2]+1)])%f)


def rp(q,g,B,W):
    a=[B(0)]*(q.degrees()[1]+1)
    for (i,j,k),v in q.to_dict().items():
        assert i==0
        a[j]+=reduce_coef(v,P)*g**k
    return W(a)


def qp(q,r,g,B,W):
    a=[B(0)]*(q.degrees()[0]+1)
    for (i,j,k),v in q.to_dict().items():
        a[i]+=reduce_coef(v,P)*r**j*g**k
    return W(a)


def check():
    F,B,gs=cuts()
    aux=auxiliary(F[0],F[2])
    total=Counter()
    for p,e in diag():
        key=p.degree(),e
        if key in ((1,72),(4,45)):
            continue  # actual gamma and Pi guards, identified exactly in diag.
        m=modpoly(p)
        if key==(566,1):
            assert m.gcd(aux)==1
            total[key]+=1
            continue
        if key in GUARDS:
            i,lower=GUARDS[key]
            assert small_exact_guard(F,gs[i],p)==lower
            nominal=[15,25,28]
        elif key==(3,1):
            nominal=[effective_degree(f,p) for f in F]
            assert nominal==[14,24,26]
            lower=0
        else:
            assert key==(144,2)
            nominal=[15,25,28]
            lower=1
        for a,e0 in factors(m):
            Q=fq_default_ctx(modulus=fmpz_mod_poly_ctx(P)(
                [int(x) for x in a.coeffs()]),var="g")
            g=Q.gen()
            W=fq_default_poly_ctx(Q)
            R=[rp(f,g,Q,W) for f in F]
            assert [q.degree() for q in R]==nominal
            d=R[0].gcd(R[1]).gcd(R[2])
            assert d.degree()==lower
            if key==(144,2):
                r=-d[0]/d[1]
                q=[qp(z,r,g,Q,W) for z in B]
                assert [z.degree() for z in q]==[2,-1,1,1]
                assert q[0].gcd(q[2]).gcd(q[3])==1
            total[key]+=1
    assert total==Counter({(566,1):1,(144,2):3,(3,1):1,(12,1):3,
                           (42,1):5,(3,2):1,(30,2):2,(12,3):4,(4,6):2})
    print("all protected exact and residue branches excluded",dict(sorted(total.items())),flush=True)


if __name__=="__main__":
    check()

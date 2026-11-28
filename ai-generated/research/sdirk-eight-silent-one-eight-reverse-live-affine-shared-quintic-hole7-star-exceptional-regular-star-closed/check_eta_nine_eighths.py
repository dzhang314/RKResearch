"""Full residual cubic-sixth eta=9/8 case, independent of the ordinary-star projection."""
from compact_star_head import basis, g, co, guard, monicq, small_exact_guard
from check_regular_star import P,modpoly,factors,rp
from flint import fmpq_poly,fmpz_mod_poly_ctx,fq_default_ctx,fq_default_poly_ctx
from phase_field import Ext,tail_cuts,gcd
from functools import reduce
from collections import Counter


def model():
    Q,_,H,_,gs,abc,(h,U,V)=basis()
    A,B,L=abc
    S0,S1=18*h-2*B+L*g,5*L
    J=9*U-8*g*g*V
    assert J.degrees()[0]==3
    homogeneous=lambda p,n:sum(co(p,i)*S0**i*S1**(n-i) for i in range(n+1))
    X,xe=guard(homogeneous(Q,2),gs)
    Y,ye=guard(homogeneous(J,3),gs)
    assert X.degrees()==(0,6,12) and xe==[2,0,1,0,0,0,0,0,0]
    assert Y.degrees()==(0,9,22) and ye==[0]*9
    R=X.resultant(Y,1)
    assert R.degrees()==(0,0,222)
    b=R.to_dict()
    p=monicq(fmpq_poly([b.get((0,0,i),0) for i in range(223)]))
    F=[(monicq(u),e) for u,e in p.factor()[1]]
    assert sorted((v.degree(),e) for v,e in F)==[(1,36),(4,18),(12,3),(78,1)]
    full=fmpq_poly([1])
    for v,e in F:full*=v**e
    assert full==p
    assert (fmpq_poly([0,1]),36) in F
    assert (monicq(fmpq_poly([1,-20,180,-840,1400])),18) in F
    return (X,Y),F,gs,H,(h,L,S0,S1)


def check():
    R,F,gs,H,data=model()
    done=Counter()
    for G,e in F:
        n=G.degree()
        if n in (1,4):continue
        if n==12:
            assert small_exact_guard(R,gs[2],G)==1
            want=[5,7]
        else:
            assert n==78
            want=[11,29,38]
        parts=factors(modpoly(G))
        assert sorted((p.degree(),e) for p,e in parts)==[(d,1) for d in want]
        for m,em in parts:
            C=fq_default_ctx(modulus=fmpz_mod_poly_ctx(P)(
                [int(z) for z in m.coeffs()]),var="g")
            W=fq_default_poly_ctx(C)
            g=C.gen()
            rd=lambda q:rp(q,g,C,W)
            x,y=[rd(q) for q in R]
            assert (x.degree(),y.degree())==(6,9)
            common=x.gcd(y)
            assert common.degree()==1
            if n==12:
                done[n,"true alpha guard"]+=1
                continue
            A=Ext(C,W,common)
            r=A.gen()
            cv=lambda q:A(rd(q))
            h,L,n0,n1=map(cv,data)
            assert h!=0 and L!=0 and n1!=0 and g!=0
            g0=A(g)
            s=n0/(n1*g0)
            y=(3*s-1)/2
            w=g0*y-9*h/L
            Hp=list(map(cv,H))
            assert len(Hp)==5 and Hp[-1]==L
            Hp=[x/L for x in Hp]
            for mode in ("star","arith","silent8"):
                F1,B,T=tail_cuts(A,g0,r,s,y,w,Hp,mode)
                d=gcd(F1,reduce(gcd,B))
                assert d==[A(1)] and gcd(d,T)==[A(1)]
                done[n,mode]+=1
    assert done==Counter({(12,"true alpha guard"):2,(78,"star"):3,
                            (78,"arith"):3,(78,"silent8"):3})
    print("eta=9/8: exact 222 diagonal, full degree12 true alpha guard;",
          "all degree78 signed rear fibers excluded",flush=True)


if __name__=="__main__":
    check()

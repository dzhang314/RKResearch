"""Complete true f1=0 exclusion, exceptional star seventh hole."""
from front_pivot import (basis,co,prem,guard,small_exact_guard,monicq,
                         fmpq_poly,reduce_coef)
from phase_field import Ext,tail_cuts,gcd
from flint import fq_default_ctx,fq_default_poly_ctx,fmpz_mod_poly_ctx,nmod_poly
from collections import Counter
from functools import reduce

P=1009


def fact(f):
    z=f**0
    out=f.factor()[1]
    for q,e in out:z*=q**e
    assert z==f
    return out


def read_r(p,g,C,V):
    a=[C(0)]*(p.degrees()[1]+1)
    for (i,j,k),c in p.to_dict().items():
        assert not i
        a[j]+=reduce_coef(c,P)*g**k
    return V(a)


def check():
    Q,F,H,gs,abc,h=basis()
    f,fe=guard(prem(F,Q),gs)
    assert f.degrees()==(1,9,19) and fe==[2,0,1,1,0,0,0,0,0]
    f0,f1=co(f,0),co(f,1)
    assert f0.degrees()==(0,9,19) and f1.degrees()==(0,9,18)
    R=f0.resultant(f1,1)
    assert R.degrees()==(0,0,306)
    tab=R.to_dict()
    o=monicq(fmpq_poly([tab.get((0,0,i),0) for i in range(307)]))
    F=[(monicq(f),e) for f,e in o.factor()[1]]
    assert sorted((f.degree(),e) for f,e in F)==[(1,54),(4,6),(4,12),(12,3),(144,1)]
    z=fmpq_poly([1])
    for f,e in F:z*=f**e
    assert z==o
    assert (fmpq_poly([0,1]),54) in F
    assert (monicq(fmpq_poly([1,-20,180,-840,1400])),12) in F
    assert (monicq(fmpq_poly([1,-20,180,-840,1680])),6) in F

    hist=Counter()
    for d,n in F:
        row=d.degree(),n
        if row in ((1,54),(4,12)):continue
        if row==(4,6):
            gdeg,want=3,[1,3]
        elif row==(12,3):
            gdeg,want=1,[1,3,4,4]
        else:
            assert row==(144,1)
            gdeg,want=1,[6,8,130]
        if row!=(144,1):
            assert small_exact_guard([f0,f1],gs[2],d)==gdeg
        D=nmod_poly([reduce_coef(c,P) for c in d.coeffs()],P)
        assert D.degree()==d.degree() and D.leading_coefficient()==1
        up=fact(D)
        assert sorted((f.degree(),m) for f,m in up)==[(n,1) for n in want]
        for e,k in up:
            C=fq_default_ctx(modulus=fmpz_mod_poly_ctx(P)(
                [int(c) for c in e.coeffs()]),var="g")
            V=fq_default_poly_ctx(C)
            g=C.gen()
            u,v=[read_r(p,g,C,V) for p in (f0,f1)]
            assert (u.degree(),v.degree())==(9,9)
            rpoly=u.gcd(v)
            assert rpoly.degree()==gdeg
            if row!=(144,1):
                hist[row]+=1
                continue
            r=-rpoly[0]/rpoly[1]
            rr=lambda P:read_r(P,g,C,V)(r)
            A,B,L=map(rr,abc)
            h0=rr(h)
            assert g!=0 and L!=0 and h0!=0
            Q=V([A,B,L])/L
            assert Q.degree()==2
            H0=[rr(P)/L for P in H]
            assert H0[-1]==1
            qs=fact(Q)
            assert sorted((q.degree(),e) for q,e in qs)==(
                [(1,1),(1,1)] if e.degree()==8 else [(2,1)])
            for a,j in qs:
                E=Ext(C,V,a)
                q=E.gen()
                g0=E(g)
                s=q/g0
                y=(3*s-1)/2
                eta=(E(B)+E(L)*g0*(s+y))/(8*E(h0))
                lam=g0*E(L)/(8*E(h0))
                d2=(1680*g0**4-840*g0**3+180*g0*g0-20*g0+1)/4
                d1=-1680*g0**4+1050*g0**3-270*g0*g0+35*g0-2
                d0=(2520*g0**4-1680*g0**3+540*g0*g0-120*g0+11)/4
                ell0=4*(1-2*d0)/3
                ell1=8*(d2-70*g0**4)
                D=d2*s*s+d1*s+d0
                U=ell0+ell1*y+4*D*(5-s)/3
                L1=D*(8-64*eta)-(9-8*eta)*ell1
                assert D!=0 and L1!=0 and lam!=0
                w=g0*(y+(-eta-(9-8*eta)*(d2-lam*U)/L1)/lam)
                HE=list(map(E,H0))
                for mode in ("star","arith","silent8"):
                    Ftail,Bs,T=tail_cuts(E,g0,E(r),s,y,w,HE,mode)
                    c=gcd(Ftail,reduce(gcd,Bs))
                    assert c==[E(1)] and gcd(c,T)==[E(1)]
                    hist[mode]+=1
    assert hist==Counter({(4,6):2,(12,3):4,"star":4,"arith":4,"silent8":4})
    print("exact gamma306; d2 and degree12 true C_N guard;",
          "full degree144 r and q fibers: all signed phase gcds one",flush=True)


if __name__=="__main__":
    check()

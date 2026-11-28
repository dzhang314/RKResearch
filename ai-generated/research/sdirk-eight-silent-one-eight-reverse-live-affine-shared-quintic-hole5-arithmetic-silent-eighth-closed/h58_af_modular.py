"""Complete local fibers for actual silent 8, with independent literal terminal minors."""
from h58_af_projection import project,gap_law,model,Co
from h58_af_shape import shape
from h567_af_ar_modular import choose_monic
from h5_star_modular import unit,rry
from h5_rank_check import signed_rows
from aq_rear import g
from aq_modular import lcmo,horner,Bfield,nmod_poly,gcdp,ev,det
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from itertools import combinations
from sympy import sqrt_mod

def test(p,t):
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    Wpol,F,data=shape()
    M,P,Q=project()
    md=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert md.degree()==M.degree() and md.leading_coefficient()==1
    fac=md.factor()[1]
    pr=nmod_poly([1],p)
    for q,e in fac:pr*=q**e
    assert pr==md
    done=[];bad=[]
    for q,e in fac:
        B0=Bfield(q,p,t);key=(q.degree(),e);qstr=str(q)
        lp,lq=[lcmo(B0,Co(T)) for T in (P,Q)]
        if len(lp)!=P.degrees()[0]+1 and len(lq)!=Q.degrees()[0]+1:
            bad.append(('Y lead',key,qstr));continue
        yp=gcdp(lp,lq)
        assert yp and yp[-1]==1
        key+=(len(yp)-1,)
        if len(yp)==1:
            done.append(('no Y',key));continue
        U,y,I=extend(B0,yp)
        uy=lambda T:rry(B0,T,y,I)
        ua,ub=[[uy(v) for v in Co(T,1)] for T in (F,gap_law())]
        up=choose_monic([ua,ub])
        if up is None:
            bad.append(('u lead',key,qstr,[unit(uy(z)) for z in gs]));continue
        assert up and up[-1]==1
        key+=(len(up)-1,)
        if len(up)==1:
            done.append(('no u',key));continue
        V,u,I0=extend(U,up)
        uv=lambda T:I0(uy(T))
        uv2=lambda T:horner([uv(c) for c in Co(T,1)],u)
        us=[horner(list(map(I0,R)),u) for R in (ua,ub)]
        js,zs=[[uv(v) for v in Co(T,1)] for T in (J,Z)]
        term=[list(map(uv2,R)) for R in Wpol]
        sp=choose_monic([js,zs,term[0]])
        if sp is None:
            bad.append(('s lead',key,qstr,[unit(uv(h)) for h in gs]));continue
        assert sp and sp[-1]==1
        key+=(len(sp)-1,)
        if len(sp)==1:
            done.append(('no s',key));continue
        W,s,I1=extend(V,sp)
        f1=[I1(h) for h in us]+[horner(list(map(I1,R)),s) for R in [js,zs]+term]
        cv=lambda T:I1(uv(T))
        a0,b0,r0,g0,be=map(cv,(a,b,r,g,B))
        c,x0,z,k,ph=map(lambda T:I1(uv2(T)),data)
        H0=list(map(cv,H))
        pegs=[a0,b0,g0*s,c,x0]
        signed,Eprime=signed_rows(W,H0,be,r0,pegs)
        Ac,Ax=ev(H0,c)*ev(Eprime,c),ev(H0,x0)*ev(Eprime,x0)
        signed.append([Ac*c**i-Ax*x0**i for i in range(3)])
        gates=[det(list(r)) for r in combinations(signed,3)]
        try:span_unit(W,*f1,*gates)
        except ArithmeticError:
            bad.append(('sat',key,qstr,[unit(cv(h)) for h in gs],[unit(z) for z in f1+gates]));continue
        done.append(('weight',key))
    assert len(done)+len(bad)==len(fac)
    print('arithmetic-front true silent8 mass-free complete',p,t,M.degree(),
          'done',done,'bad',bad,flush=True)
    return len(done),bad

if __name__=='__main__':
    import argparse
    A=argparse.ArgumentParser()
    A.add_argument('--p',type=int,default=1129);A.add_argument('--t',type=int)
    a=A.parse_args()
    t=a.t or int(sqrt_mod(pow(2,-1,a.p),a.p))
    test(a.p,t)

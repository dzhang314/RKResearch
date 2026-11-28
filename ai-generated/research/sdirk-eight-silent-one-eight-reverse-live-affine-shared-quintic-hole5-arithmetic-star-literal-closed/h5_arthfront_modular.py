"""Complete local fibers for the two independent actual arithmetic front placements."""
from h5_arthfront_projection import model,edges,diagonal,Co,g
from h5_star_modular import unit,rry
from h5_rank_check import signed_rows
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp,det
from aq_modular import ev as at
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from itertools import combinations

def test(slot,p,t):
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    F,E,O=edges(False,slot)
    M,P,Q=diagonal(slot)
    md=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert md.degree()==M.degree() and md.leading_coefficient()==1
    parts=md.factor()[1]
    prod=nmod_poly([1],p)
    for h,e in parts:prod*=h**e
    assert prod==md
    done=[];bad=[]
    for f,e in parts:
        N=Bfield(f,p,t);key=(f.degree(),e);fp=str(f)
        Sy,Ty=[lcmo(N,Co(T)) for T in (P,Q)]
        if len(Sy)!=P.degrees()[0]+1 and len(Ty)!=Q.degrees()[0]+1:
            bad.append(('Y leading',key,fp));continue
        T0=gcdp(Sy,Ty)
        assert T0 and T0[-1]==1
        key+=(len(T0)-1,)
        if len(T0)==1:
            done.append(('no_Y',key));continue
        U,y,I=extend(N,T0)
        cvy=lambda T:rry(N,T,y,I)
        j0,z0=[[cvy(v) for v in Co(T,1)] for T in (J,Z)]
        jl,zl=unit(j0[-1]),unit(z0[-1])
        if not jl and not zl:
            bad.append(('s leading',key,fp,[unit(cvy(v)) for v in gs]));continue
        try:
            R0=gcdp(j0,z0)
            assert R0 and R0[-1]==1
        except ArithmeticError:
            R0=mon(j0 if jl else z0)
        key+=(len(R0)-1,)
        if len(R0)==1:
            done.append(('no_s',key));continue
        V,s,I0=extend(U,R0)
        cv=lambda T:I0(cvy(T))
        F0,F1=map(cv,Co(F,1))
        if not unit(F1):
            bad.append(('w leading',key,fp,[unit(cv(v)) for v in gs]));continue
        w=-F0/F1
        early=[horner(list(map(I0,R)),s) for R in (j0,z0)]
        early +=[horner(list(map(cv,Co(T,1))),w) for T in (E,O)]
        try:
            span_unit(V,*early)
            done.append(('no_w',key));continue
        except ArithmeticError:pass
        W,v,I1=extend(V,[-w,V(0),V(1)])
        cc=lambda T:I1(cv(T))
        a0,b0,g0,r0,x0,be=map(cc,(a,b,g,r,x,B))
        c,d=x0-g0*(1+v),x0-g0*(1-v)
        pegs=[b0 if slot==2 else a0,g0*I1(s),d,c,x0]
        H0=list(map(cc,H))
        rows,Ec=signed_rows(W,H0,be,r0,pegs)
        Ac=at(H0,c)*at(Ec,c);Ax=at(H0,x0)*at(Ec,x0)
        rows.append([Ac*c**i-Ax*x0**i for i in range(3)])
        vals=list(map(I1,early))+[det(list(Q0)) for Q0 in combinations(rows,3)]
        try:span_unit(W,*vals)
        except ArithmeticError:
            bad.append(('signed',key,fp,[unit(cc(q)) for q in gs],[unit(v0) for v0 in vals]));continue
        done.append(('weight',key))
    assert len(done)+len(bad)==len(parts)
    print('arithmetic front star rear literal complete',slot,p,t,M.degree(),'done',done,'bad',bad,flush=True)
    return len(done),bad

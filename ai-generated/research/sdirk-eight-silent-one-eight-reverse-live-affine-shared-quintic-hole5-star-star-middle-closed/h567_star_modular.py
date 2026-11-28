"""Full exact and modular fibers retaining the actual monic linear cofactor."""
from h567_star_projection import project,signed_model,model,Co,g
from functools import lru_cache
from h5_star_modular import unit,rry
from h5_rank_check import W
from aq_modular import (lcmo,mon,horner,Bfield,nmod_poly,gcdp,det as fdet,
    nodal,ev as at,add,mul,sc)
from arith_ordinary_reconstruction import extend,factor_deriv
from gauss_separate import span_unit
from itertools import combinations
from unequal_finite import E

@lru_cache(None)
def exact_gamma(cubic):
    aa=project(cubic,False)
    dd=project(cubic,True)
    assert len(aa)==len(dd)
    out=[]
    for (M,P,Q,kind),(N,P1,R,kind1) in zip(aa,dd):
        assert P==P1 and kind==kind1
        assert not M.b and not N.b
        D=E(M.a.gcd(N.a)).monic()
        print('six-peg exact diagonal gcd',cubic,kind,M.degree(),N.degree(),D.degree(),flush=True)
        assert D.degree()==(54 if cubic else 3 if kind=='degenerate' else 30)
        out.append((D,P,Q,R,kind))
    return tuple(out)

def minors(Wf,H,be,r,pegs):
    e=nodal(pegs);de=factor_deriv(e,Wf)
    hr=at(H,r);wh=W(Wf,H,hr,be,r)
    cols=[]
    for j in range(2):
        p=[Wf(0)]*j+e
        z=add(mul(H,W(Wf,p,hr,be,r)),sc(mul(p,wh),-1))
        assert len(z)<=4
        cols.append((z+[Wf(0)]*(4-len(z)))[1:])
    rows=list(map(list,zip(*cols)))
    c,x=pegs[-2:]
    ac=at(de,c)*at(H,c);ax=at(de,x)*at(H,x)
    rows.append([ac-ax,ac*c-ax*x])
    return [fdet(list(rr)) for rr in combinations(rows,2)]

def test(cubic,p,t0):
    H,D,A,B,J,Z,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    C0,D1,F,_=signed_model()
    out=[]
    for M,P,Q,R,kind in exact_gamma(cubic):
        md=Bfield(nmod_poly([0,1],p),p,t0).cast(M)
        assert md.degree()==M.degree() and md.leading_coefficient()==1
        parts=md.factor()[1]
        ck=nmod_poly([1],p)
        for f,e in parts:ck*=f**e
        assert ck==md
        done=[];bad=[]
        for f,e in parts:
            N=Bfield(f,p,t0);key=(kind,f.degree(),e);fp=str(f)
            pol=[lcmo(N,Co(T)) for T in (P,Q,R)]
            if not any(len(P0)==T.degrees()[0]+1 for P0,T in zip(pol,(P,Q,R))):
                bad.append(('Y leading',key,fp));continue
            coeff=gcdp(gcdp(pol[0],pol[1]),pol[2])
            assert coeff and coeff[-1]==1
            key+=(len(coeff)-1,)
            if len(coeff)==1:
                done.append(('no_Y',key));continue
            U,y,I=extend(N,coeff)
            cvy=lambda T:rry(N,T,y,I)
            js=[]
            if cubic:
                js=[[cvy(v) for v in Co(T,1)] for T in (J,C0,D1)]
                lead=[unit(j[-1]) for j in js]
                if not any(lead):
                    bad.append(('s leading',key,fp,[unit(cvy(d)) for d in gs]));continue
                V,s,I0=extend(U,mon(js[lead.index(True)]))
            else:
                V,s,I0=U,(2*y+1)/3,lambda z:z
            cv=lambda T:I0(cvy(T))
            early=[horner(list(map(I0,j)),s) for j in js]
            try:
                if not early: raise ArithmeticError("no additional s-constraints in this branch")
                span_unit(V,*early)
                done.append(('no_s',key));continue
            except ArithmeticError:pass
            F0,F1=map(cv,Co(F,1))
            if not unit(F1):
                bad.append(('w leading',key,fp,[unit(cv(d)) for d in gs]));continue
            w=-F0/F1
            Wf,v,I1=extend(V,[-w,V(0),V(1)])
            cv2=lambda T:I1(cv(T))
            a0,b0,g0,r0,x0,be=map(cv2,(a,b,g,r,x,B))
            c,d=x0-g0*(1+v),x0-g0*(1-v)
            p4=g0*I1(s)
            H0=list(map(cv2,H))
            gates=minors(Wf,H0,be,r0,[a0,b0,p4,d,c,x0])
            try:span_unit(Wf,*map(I1,early),*gates)
            except ArithmeticError:
                bad.append(('signed',key,fp,[unit(cv2(d)) for d in gs],[unit(z) for z in gates]));continue
            done.append(('signed',key))
        assert len(done)+len(bad)==len(parts)
        print('six-peg centered residue',cubic,p,t0,kind,'kept',M.degree(),'done',done,'bad',bad,flush=True)
        out.append((len(done),bad))
    return out

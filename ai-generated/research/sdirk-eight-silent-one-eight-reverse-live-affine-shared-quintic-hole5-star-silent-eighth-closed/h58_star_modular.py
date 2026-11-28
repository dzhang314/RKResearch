"""Complete finite localization of the true ordinarily silent eighth chart."""
from functools import lru_cache
from h58_star_projection import project,signed_model,model,Co,g
from h5_rank_check import signed_rows
from h58_star_rank import affine_rank_cut
from h5_star_modular import unit,rry
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp,det,ev
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from itertools import combinations

@lru_cache(None)
def gamma_set(cubic):
    return [(affine_rank_cut(M,P,Q) if not cubic and k=="usual" else M,P,Q,k)
            for M,P,Q,k in project(cubic)]

def test(cubic,p,t):
    H,D,A,B,J,Zf,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    C,N,F,ta=signed_model()
    out=[]
    for M,P,Q,kind in gamma_set(cubic):
        d0=Bfield(nmod_poly([0,1],p),p,t).cast(M)
        assert d0.degree()==M.degree() and d0.leading_coefficient()==1
        parts=d0.factor()[1]
        chk=nmod_poly([1],p)
        for f,e in parts:chk*=f**e
        assert chk==d0
        done=[];bad=[]
        for f,e in parts:
            N0=Bfield(f,p,t)
            key=(kind,f.degree(),e);fp=str(f)
            pols=(P,Q)
            Yp=[lcmo(N0,Co(T)) for T in pols]
            if not any(len(U)==T.degrees()[0]+1 for U,T in zip(Yp,pols)):
                bad.append(('Y leading',key,fp));continue
            E0=Yp[0]
            for y0 in Yp[1:]:E0=gcdp(E0,y0)
            assert E0 and E0[-1]==1
            key+=(len(E0)-1,)
            if len(E0)==1:
                done.append(('no_Y',key));continue
            U,y,I=extend(N0,E0)
            cvy=lambda P:rry(N0,P,y,I)
            if cubic:
                J0=[cvy(j) for j in Co(J,1)]
                if not unit(J0[-1]):
                    bad.append(('s leading',key,fp,[unit(cvy(q)) for q in gs]));continue
                V,s,I0=extend(U,mon(J0))
            else:
                V,s,I0=U,(2*y+1)/3,lambda a:a
            cv=lambda P:I0(cvy(P))
            F0=[cv(q) for q in Co(F,1)]
            if not unit(F0[-1]):
                bad.append(('u leading',key,fp,[unit(cv(q)) for q in gs]));continue
            assert len(F0)==5
            T,u,I1=extend(V,mon(F0))
            s0=I1(s);cc=lambda T:I1(cv(T))
            uu=lambda P:horner(list(map(cc,Co(P,1))),u)
            ex=[horner(list(map(uu,P)),s0) for P in (C,N)]
            c,x0,z,k,ph=map(uu,ta)
            a0,b0,g0,r0,be=map(cc,(a,b,g,r,B))
            q=g0*s0
            pegs=[a0,b0,q,c,x0]
            H0=list(map(cc,H))
            rows,Ec=signed_rows(T,H0,be,r0,pegs)
            Ac=ev(H0,c)*ev(Ec,c);Ax=ev(H0,x0)*ev(Ec,x0)
            rows.append([Ac*c**j-Ax*x0**j for j in range(3)])
            gates=[det(list(K)) for K in combinations(rows,3)]
            try:span_unit(T,*ex,*gates)
            except ArithmeticError:
                bad.append(('signed',key,fp,[unit(cc(a)) for a in gs],[unit(a) for a in ex+gates],
                    [unit(k0) for k0 in (u,u-2,k,s0-y,z-x0,z-c,z-r0)]));continue
            done.append(('signed',key))
        assert len(done)+len(bad)==len(parts)
        print('true silent8 complete local',cubic,p,t,kind,'kept',M.degree(),'done',done,'bad',bad,flush=True)
        out.append((len(done),bad))
    return out

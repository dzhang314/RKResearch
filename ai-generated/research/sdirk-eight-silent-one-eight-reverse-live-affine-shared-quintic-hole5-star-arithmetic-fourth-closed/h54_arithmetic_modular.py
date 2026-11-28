"""Replay every finite component, retaining complete fifth and gap quotients."""
from h54_arithmetic_projection import model,exact_tail,project,gpoly,Co,g
from h5_star_modular import unit,rry
from h5_rank_check import signed_rows
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp,det
from aq_modular import ev as peval
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from itertools import combinations

def test(cubic,p,t0):
    H,D,A,B,J,Z,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    F,G0,G1,data=exact_tail()
    out=[];count=0
    for M,P,Q,kind in project(cubic):
        R=Bfield(nmod_poly([0,1],p),p,t0).cast(M)
        assert R.degree()==M.degree() and R.leading_coefficient()==1
        facs=R.factor()[1]
        rr=nmod_poly([1],p)
        for f,e in facs:rr*=f**e
        assert rr==R
        done=[];bad=[]
        for q,e in facs:
            N=Bfield(q,p,t0);key=(kind,q.degree(),e);qp=str(q)
            pn,qn=[lcmo(N,Co(T)) for T in (P,Q)]
            if len(pn)!=P.degrees()[0]+1 and len(qn)!=Q.degrees()[0]+1:
                bad.append(('Y leading',key,qp));continue
            E=gcdp(pn,qn)
            assert E and E[-1]==1
            key+=(len(E)-1,)
            if len(E)==1:
                done.append(('no_Y',key));continue
            U,y,I=extend(N,E)
            cvy=lambda T:rry(N,T,y,I)
            if cubic:
                J0=[cvy(v) for v in Co(J,1)]
                if not unit(J0[-1]):
                    bad.append(('s leading',key,qp,[unit(cvy(d)) for d in gs]));continue
                V,s,I0=extend(U,mon(J0))
            else:
                V,s,I0=U,(2*y+1)/3,lambda z:z
            cv=lambda T:I0(cvy(T))
            Fp,Gp0,Gp1=[[cv(v) for v in Co(T,1)] for T in (F,G0,G1)]
            Gp=[z0+s*z1 for z0,z1 in zip(Gp0,Gp1)]
            if not unit(Fp[-1]) and not unit(Gp[-1]):
                bad.append(('u leading',key,qp,[unit(cv(d)) for d in gs]));continue
            try:
                Dp=gcdp(Fp,Gp)
                assert Dp and Dp[-1]==1
            except ArithmeticError:
                Dp=mon(Fp if unit(Fp[-1]) else Gp)
            if len(Dp)==1:
                done.append(('no_u',key));continue
            W,u,I1=extend(V,Dp)
            hh=lambda T:horner([I1(cv(v)) for v in Co(T,1)],u)
            early=[horner(list(map(I1,Q)),u) for Q in (Fp,Gp)]
            if all(not z for z in early):early=[]
            cv2=lambda T:I1(cv(T))
            a0,b0,g0,r0,x0,be=map(cv2,(a,b,g,r,x,B))
            c,d,k=map(hh,data)
            pegs=[a0,b0,x0,c,d]
            H0=list(map(cv2,H))
            rows,En=signed_rows(W,H0,be,r0,pegs)
            Ac=peval(H0,c)*peval(En,c);Ax=peval(H0,x0)*peval(En,x0)
            rows.append([Ac*c**j-Ax*x0**j for j in range(3)])
            try:span_unit(W,*early,*[det(list(M)) for M in combinations(rows,3)])
            except ArithmeticError:
                bad.append(('signed',key,qp,[unit(cv2(d)) for d in gs]));continue
            done.append(('weight',key+(len(Dp)-1,)))
        assert len(done)+len(bad)==len(facs)
        print('arithmetic corrected hole5 silent4 complete',cubic,p,t0,kind,'kept',M.degree(),'done',done,'bad',bad,flush=True)
        out+=bad;count+=len(done)
    return count,out

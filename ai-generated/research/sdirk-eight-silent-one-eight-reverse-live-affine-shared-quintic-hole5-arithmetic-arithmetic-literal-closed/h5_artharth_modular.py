"""Complete local arithmetic-rear fibers with true ordinary nonhole pegs."""
from h5_artharth_projection import rear,diagonal,model,Co,g
from h5_star_modular import unit,rry
from h5_rank_check import signed_rows
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp,det,ev
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from itertools import combinations

def fullmon(A,B):
    al,bl=unit(A[-1]),unit(B[-1])
    if not(al or bl):return None
    try:return gcdp(A,B)
    except ArithmeticError:return mon(A if al else B)

def test(slot,p,t):
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    F,G,data=rear(slot)
    MS,P,Q=diagonal(slot)
    md=Bfield(nmod_poly([0,1],p),p,t).cast(MS)
    assert md.degree()==MS.degree() and md.leading_coefficient()==1
    parts=md.factor()[1]
    prod=nmod_poly([1],p)
    for h,e in parts:prod*=h**e
    assert prod==md
    done=[];bad=[]
    for f,e in parts:
        N=Bfield(f,p,t);key=(f.degree(),e);fp=str(f)
        Py,Qy=[lcmo(N,Co(T)) for T in (P,Q)]
        if len(Py)!=P.degrees()[0]+1 and len(Qy)!=Q.degrees()[0]+1:
            bad.append(('Y leading',key,fp));continue
        Yp=gcdp(Py,Qy)
        assert Yp and Yp[-1]==1
        key+=(len(Yp)-1,)
        if len(Yp)==1:
            done.append(('no_Y',key));continue
        U,y,I=extend(N,Yp)
        cvy=lambda T:rry(N,T,y,I)
        J0,Z0=[[cvy(v) for v in Co(T,1)] for T in (J,Z)]
        Sp=fullmon(J0,Z0)
        if Sp is None:
            bad.append(('s leading',key,fp,[unit(cvy(v)) for v in gs]));continue
        assert Sp and Sp[-1]==1
        key+=(len(Sp)-1,)
        if len(Sp)==1:
            done.append(('no_s',key));continue
        V,s,I0=extend(U,Sp)
        cv=lambda T:I0(cvy(T))
        F0,G0=[[cv(v) for v in Co(T,1)] for T in (F,G)]
        Up=fullmon(F0,G0)
        if Up is None:
            bad.append(('u leading',key,fp,[unit(cv(v)) for v in gs]));continue
        assert Up and Up[-1]==1
        key+=(len(Up)-1,)
        if len(Up)==1:
            done.append(('no_u',key));continue
        W,u,I1=extend(V,Up)
        early=[I1(horner(list(map(I0,R)),s)) for R in (J0,Z0)]
        early +=[horner(list(map(I1,R)),u) for R in (F0,G0)]
        cc=lambda T:I1(cv(T))
        uu=lambda T:horner(list(map(cc,Co(T,1))),u)
        a0,b0,g0,r0,x0,be=map(cc,(a,b,g,r,x,B))
        c,d,k=map(uu,data)
        pegs=[b0 if slot==2 else a0,g0*I1(s),d,c,x0]
        H0=list(map(cc,H))
        rows,Ec=signed_rows(W,H0,be,r0,pegs)
        Ac=ev(H0,c)*ev(Ec,c);Ax=ev(H0,x0)*ev(Ec,x0)
        rows.append([Ac*c**i-Ax*x0**i for i in range(3)])
        vals=early+[det(list(Q0)) for Q0 in combinations(rows,3)]
        try:span_unit(W,*vals)
        except ArithmeticError:
            bad.append(('signed',key,fp,[unit(cc(q)) for q in gs],[unit(v0) for v0 in vals]));continue
        done.append(('weight',key))
    assert len(done)+len(bad)==len(parts)
    print('arithmetic front arithmetic rear literal complete',slot,p,t,MS.degree(),'done',done,'bad',bad,flush=True)
    return len(done),bad

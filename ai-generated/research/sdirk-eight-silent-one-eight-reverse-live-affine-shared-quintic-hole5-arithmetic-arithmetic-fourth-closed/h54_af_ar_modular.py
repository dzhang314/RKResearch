"""Complete arithmetic-front/rear silent fourth, without guessing an affine pivot."""
from h54_af_ar_projection import project,tails,model,Co,g
from h5_star_modular import unit,rry
from h5_rank_check import signed_rows
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp,det,ev,add,sc,mul
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from itertools import combinations

def test(p,t):
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    F,G0,G1,data=tails()
    M,P,Q=project()
    md=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert md.degree()==M.degree() and md.leading_coefficient()==1
    fac=md.factor()[1]
    prod=nmod_poly([1],p)
    for f,e in fac:prod*=f**e
    assert prod==md
    done=[];bad=[]
    for q,e in fac:
        B0=Bfield(q,p,t);key=(q.degree(),e);qp=str(q)
        py,qy=[lcmo(B0,Co(T)) for T in (P,Q)]
        if len(py)!=P.degrees()[0]+1 and len(qy)!=Q.degrees()[0]+1:
            bad.append(('Y leading',key,qp));continue
        Yp=gcdp(py,qy)
        assert Yp and Yp[-1]==1
        key+=(len(Yp)-1,)
        if len(Yp)==1:
            done.append(('no_Y',key));continue
        U,y,I=extend(B0,Yp)
        cvy=lambda T:rry(B0,T,y,I)
        Fs,Ga,Gb,Js,Zs=[[cvy(v) for v in Co(T,1)] for T in (F,G0,G1,J,Z)]
        if not unit(Fs[-1]):
            bad.append(('u leading',key,qp,[unit(cvy(v)) for v in gs]));continue
        j0,j1,j2=Js
        C0=add(add(sc(mul(Ga,Ga),j2),sc(mul(Ga,Gb),-j1)),sc(mul(Gb,Gb),j0))
        try:Up=gcdp(Fs,C0)
        except ArithmeticError:Up=mon(Fs)
        assert Up and Up[-1]==1
        key+=(len(Up)-1,)
        if len(Up)==1:
            done.append(('no_u',key));continue
        V,u,I0=extend(U,Up)
        cva=lambda T:I0(cvy(T))
        aa=lambda Q:horner(list(map(I0,Q)),u)
        g0,g1=aa(Ga),aa(Gb)
        Spats=[[g0,g1],list(map(I0,Js)),list(map(I0,Zs))]
        piv=[R for R in Spats if unit(R[-1])]
        if not piv:
            bad.append(('s leading',key,qp,[unit(cva(q)) for q in gs]));continue
        try:Sp=gcdp(gcdp(Spats[0],Spats[1]),Spats[2])
        except ArithmeticError:Sp=mon(piv[0])
        assert Sp and Sp[-1]==1
        key+=(len(Sp)-1,)
        if len(Sp)==1:
            done.append(('no_s',key));continue
        W,s,I1=extend(V,Sp)
        cv=lambda T:I1(cva(T))
        early=[I1(aa(q)) for q in (Fs,C0)] + [horner(list(map(I1,q)),s) for q in Spats]
        c,d,k=map(lambda T:I1(aa(list(map(cvy,Co(T,1))))),data)
        x0,a0,b0,r0,be,ga=map(cv,(x,a,b,r,B,g))
        z=ga*s
        H0=list(map(cv,H))
        early.append((x0-z)*ev(H0,c)-k*(c-z)*ev(H0,x0))
        rows,Ec=signed_rows(W,H0,be,r0,[a0,b0,d,c,x0])
        Ac=ev(H0,c)*ev(Ec,c);Ax=ev(H0,x0)*ev(Ec,x0)
        rows.append([Ac*c**i-Ax*x0**i for i in range(3)])
        vals=early+[det(list(rs)) for rs in combinations(rows,3)]
        try:span_unit(W,*vals)
        except ArithmeticError:
            bad.append(('signed',key,qp,[unit(cv(v)) for v in gs],[unit(v) for v in vals]));continue
        done.append(('weight',key))
    assert len(done)+len(bad)==len(fac)
    print('arithmetic-front arithmetic-rear true silent4 complete',p,t,M.degree(),
          'done',done,'bad',bad,flush=True)
    return len(done),bad

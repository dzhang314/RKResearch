"""Full local arithmetic-front/star-rear silent fourth with actual z=c4."""
from h54_af_star_projection import project,U,model,Co,g
from h5_star_modular import unit,rry
from h5_rank_check import signed_rows
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp,det,ev
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from itertools import combinations

def test(p,t):
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    V0,F,A0=U()
    M,P,C,N=project()
    md=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert md.degree()==M.degree() and md.leading_coefficient()==1
    parts=md.factor()[1]
    prod=nmod_poly([1],p)
    for f,e in parts:prod*=f**e
    assert prod==md
    done=[];bad=[]
    for f,e in parts:
        B0=Bfield(f,p,t);key=(f.degree(),e);fp=str(f)
        expr=(P,C,N);yp=[lcmo(B0,Co(Q)) for Q in expr]
        if not any(len(Q)==T.degrees()[0]+1 for Q,T in zip(yp,expr)):
            bad.append(('Y leading',key,fp));continue
        Yp=gcdp(gcdp(yp[0],yp[1]),yp[2])
        assert Yp and Yp[-1]==1
        key+=(len(Yp)-1,)
        if len(Yp)==1:
            done.append(('no_Y',key));continue
        V,y,I=extend(B0,Yp)
        cvy=lambda Q:rry(B0,Q,y,I)
        Rv=[[cvy(v) for v in Co(Q,1)] for Q in (V0,J,Z)]
        pivot=[R for R in Rv if unit(R[-1])]
        if not pivot:
            bad.append(('s leading',key,fp,[unit(cvy(q)) for q in gs]));continue
        try:Sp=gcdp(gcdp(Rv[0],Rv[1]),Rv[2])
        except ArithmeticError:Sp=mon(pivot[0])
        assert Sp and Sp[-1]==1
        key+=(len(Sp)-1,)
        if len(Sp)==1:
            done.append(('no_s',key));continue
        S,s,I0=extend(V,Sp)
        cv=lambda Q:I0(cvy(Q))
        F0,F1=map(cv,Co(F,1))
        if not unit(F1):
            bad.append(('w leading',key,fp,[unit(cv(q)) for q in gs]));continue
        w=-F0/F1
        W,v,I1=extend(S,[-w,S(0),S(1)])
        cc=lambda Q:I1(cv(Q))
        a0,b0,g0,r0,x0,be=map(cc,(a,b,g,r,x,B))
        s0=I1(s);z=g0*s0;k=2-v*v
        c,d=x0-g0*(1+v),x0-g0*(1-v)
        H0=list(map(cc,H))
        early=[I1(horner(list(map(I0,Q)),s)) for Q in Rv]
        early.append((x0-z)*ev(H0,c)-k*(c-z)*ev(H0,x0))
        rows,Ec=signed_rows(W,H0,be,r0,[a0,b0,d,c,x0])
        Ac=ev(H0,c)*ev(Ec,c);Ax=ev(H0,x0)*ev(Ec,x0)
        rows.append([Ac*c**i-Ax*x0**i for i in range(3)])
        vals=early+[det(list(Q)) for Q in combinations(rows,3)]
        try:span_unit(W,*vals)
        except ArithmeticError:
            bad.append(('signed',key,fp,[unit(cc(q)) for q in gs],[unit(w) for w in vals]));continue
        done.append(('weight',key))
    assert len(done)+len(bad)==len(parts)
    print('silent4 arithmetic-front star-rear complete',p,t,M.degree(),'done',done,'bad',bad,flush=True)
    return len(done),bad

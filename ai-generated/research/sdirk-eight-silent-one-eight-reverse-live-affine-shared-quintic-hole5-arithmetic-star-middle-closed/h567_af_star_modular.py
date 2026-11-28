"""Complete local fibers for both real physical ordinary-silent middle positions."""
from h567_af_star_projection import project,model,Co
from h567_af_star_shape import signed_model
from h567_star_modular import minors
from h5_rank_check import W as Wseries
from itertools import combinations
from h5_star_modular import unit,rry
from aq_rear import g
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp,nodal,ev,add,mul,sc,det
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit

def normalized_signed_minors(V,H,beta,r,pegs):
    """Independent division by the true signed mass, no residue inverse."""
    E=nodal(pegs)
    hr=ev(H,r)
    def bez(D,hh,bb):
        return add(mul(H,Wseries(V,D,hh,bb,r)),sc(mul(D,Wseries(V,H,hh,bb,r)),-1))
    base=bez(E,hr,beta)
    nxt=add(bez(mul([-r,V(1)],E),V(1),V(0)),sc(E,-beta))
    rows=[[(base[j] if j<len(base) else V(0)),(nxt[j] if j<len(nxt) else V(0))]
          for j in (1,2,3)]
    return [det(list(q)) for q in combinations(rows,2)]

def fully_mass_free_minors(V,H,beta,r,pegs):
    """Absorb the paid scalar nodal equation before canceling the signed mass."""
    Xr=[-r,V(1)]
    E=nodal(pegs)
    def col(D):
        WD,WH=[Wseries(V,P,V(1),V(0),r) for P in (D,H)]
        BI=add(mul(H,WD),sc(mul(D,WH),-1))
        m=sum((V(c)/(i+1) for i,c in enumerate(D)),V(0))
        return add(add(mul(Xr,BI),sc(D,-beta)),sc(H,m))
    d0,d1=col(E),col([V(0)]+E)
    assert len(d0)<=5 and len(d1)<=5
    A0=d0+[V(0)]*(5-len(d0));A1=d1+[V(0)]*(5-len(d1))
    rows=[[A0[j],A1[j]] for j in (2,3,4)]
    c,x=pegs[-2:]
    Ed=[i*E[i] for i in range(1,len(E))]
    ac=ev(H,c)*ev(Ed,c);ax=ev(H,x)*ev(Ed,x)
    rows.append([ac-ax,c*ac-x*ax])
    return [det(list(q)) for q in combinations(rows,2)]

def test(p,t):
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    C,N,F,_=signed_model()
    M,P,QC,QN=project()
    md=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert md.degree()==M.degree() and md.leading_coefficient()==1
    parts=md.factor()[1]
    prod=nmod_poly([1],p)
    for q,e in parts:prod*=q**e
    assert prod==md
    done=[];bad=[]
    for q,e in parts:
        B0=Bfield(q,p,t);key=(q.degree(),e);qq=str(q)
        Qy=[lcmo(B0,Co(T)) for T in (P,QC,QN)]
        if not any(len(q)==F0.degrees()[0]+1 for q,F0 in zip(Qy,(P,QC,QN))):
            bad.append(('Y leading',key,qq));continue
        Yp=gcdp(gcdp(Qy[0],Qy[1]),Qy[2])
        assert Yp and Yp[-1]==1
        key+=(len(Yp)-1,)
        if len(Yp)==1:
            done.append(('no_Y',key));continue
        U,y,I=extend(B0,Yp)
        cvy=lambda T:rry(B0,T,y,I)
        Ss=[[cvy(w) for w in Co(T,1)] for T in (J,Z,C,N)]
        Ps=[u for u in Ss if unit(u[-1])]
        if not Ps:
            bad.append(('s leading',key,qq,[unit(cvy(v)) for v in gs]));continue
        try:Sp=gcdp(gcdp(Ss[0],Ss[1]),gcdp(Ss[2],Ss[3]))
        except ArithmeticError:Sp=mon(Ps[0])
        assert Sp and Sp[-1]==1
        key+=(len(Sp)-1,)
        if len(Sp)==1:
            done.append(('no_s',key));continue
        V,s,I0=extend(U,Sp)
        cv=lambda T:I0(cvy(T))
        F0,F1=map(cv,Co(F,1))
        if not unit(F1):
            bad.append(('w leading',key,qq,[unit(cv(a)) for a in gs]));continue
        w=-F0/F1
        Wf,v,I1=extend(V,[-w,V(0),V(1)])
        cc=lambda T:I1(cv(T))
        a0,b0,g0,r0,x0,be=map(cc,(a,b,g,r,x,B))
        c,d=x0-g0*(1+v),x0-g0*(1-v)
        H0=list(map(cc,H))
        ps=[I1(horner(list(map(I0,T)),s)) for T in Ss]
        pegs=[a0,b0,g0*I1(s),d,c,x0]
        gates=minors(Wf,H0,be,r0,pegs)+normalized_signed_minors(Wf,H0,be,r0,pegs)+fully_mass_free_minors(Wf,H0,be,r0,pegs)
        try:span_unit(Wf,*ps,*gates)
        except ArithmeticError:
            bad.append(('signed',key,qq,[unit(cc(x)) for x in gs],[unit(x) for x in ps+gates]));continue
        done.append(('signed',key))
    assert len(done)+len(bad)==len(parts)
    print('arithmetic front ordinary star rear actual middle complete',p,t,M.degree(),'done',done,'bad',bad,flush=True)
    return len(done),bad

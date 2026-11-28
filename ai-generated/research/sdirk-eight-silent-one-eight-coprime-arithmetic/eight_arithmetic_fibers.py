"""Regular reduced finite arithmetic fibers, with the actual literal sixth gate."""
from eight_arithmetic_projection import *
from star_fibers import eval_E,sixth_gate
from star_gauss import Nested,fixres

def ycoeffs(M):
    res=sorted({i for (i,j,k,l) in M.to_dict()})
    assert res==list(range(res[-1]+1))
    return [can(sum(v*u**j*g**k*t**l
                   for (i,j,k,l),v in M.to_dict().items() if i==iy))
            for iy in res]

def check_reg(front,p,t,verbose=True):
    R,RB,mo=projections(front)
    F0,M0,C,E5,guards,geom,de=mo
    A,B,m,ha,hb,H4,*_=phases(front)
    a,b,q,bq,*_=de
    phy=[ea(q)[0],ea(bq)[0]]
    Cp=list(map(ea,C))
    E5c=[ea(v)[0] for v in ycoeffs(E5)]
    Fp=Bfield(nmod_poly([0,1],p),p,t)
    bR=Fp.cast(R)
    assert bR.degree()==R.degree() and bR.leading_coefficient()==1
    counts=[0]*4
    for g0,e in bR.factor()[1]:
        F=Bfield(g0,p,t);gamma=F(nmod_poly([0,1],p))
        f=lambda c:eval_E(F,gamma,c)
        counts[0]+=1
        ff=list(map(f,F0));ff[-1].inv()
        mm=list(map(f,M0))
        u1=gcdp(ff,mm)
        if len(u1)<=1:continue
        U=Tower(u1);uu=U.gen()
        counts[1]+=1
        if verbose:print('arithmetic gap reduced',front,p,t,g0.degree(),len(u1)-1,flush=True)
        zz=[ev([U(f(v)) for v in pp],uu) for pp in Cp]
        ew=[U(f(v)) for v in E5c]
        try:
            zp=mon(zz); assert len(zp)==4
            yp=gcdp(zp,ew)
        except ArithmeticError:
            yp0=mon(ew); assert len(yp0)==4
            yp=gcdp(yp0,zz)
        if len(yp)<=1:continue
        counts[2]+=1
        W=Nested(yp);y=W.gen()
        ga=W(U(gamma)); L=[W(v)*ga**j for j,v in enumerate(Lco)]
        Q=[W(U(f(v))) for v in phy]
        A0,B0,m0,ha0,hb0=map(W,(U(A),U(B),U(m),U(ha),U(hb)))
        HH=[W(U(v)) for v in H4]
        ys=list(map(W,zz));assert not ev(ys,y)
        uz=ys[3];vz=ys[2]+uz*y;wz=ys[1]+vz*y
        if verbose:print('arithmetic fifth reduced',front,p,t,g0.degree(),len(u1)-1,len(yp)-1,flush=True)
        zz2=[wz,vz,uz]
        gate=sixth_gate(W,A0,B0,m0,ha0,hb0,HH,Q,L,y)
        fixres(zz2,gate,W).inv()
        counts[3]+=1
    return tuple(counts)

"""Full local residual tests for the physical shared Gauss hole."""
from shared_one_front_models import *
from unequal_finite import Bfield,Tower
from extra_active import invpoly
from gauss_separate import span_unit
from flint import nmod_poly

def frac_p(c,p):return (int(c.p)*pow(int(c.q),-1,p))%p

def ev_poly(P,ex,K,pg,rr,ts,ga,sv):
    V={}
    for (iy,ii,ig,ir,it),c in P.to_dict().items():
        if ex==0:ii,k=ii,iy
        else:ii,k=iy,ii
        b=K(frac_p(c,pg)*pow(rr,ir,pg)*pow(ts,it,pg)%pg)
        V[k]=V.get(k,K(0))+b*ga**ig*sv**ii
    return trim([V.get(i,K(0)) for i in range(max(V,default=-1)+1)])

def qf(P,gc,ga):
    return ev(list(map(gc,P)),ga)

def root_consts(p):
    q0=nmod_poly(list(Lco),p)
    aa=[int(v) for v,m0 in q0.roots() if m0==1]
    if len(aa)!=4:return None
    return sorted(aa)

def p_monic(K,rr):
    L=mon(list(map(K,Lco)))
    P,Q=qr(L,[-rr,K(1)])
    assert not Q and len(P)==4
    return P

def p_masks(K,rr,P,pegs):
    nu=sum(K(v)/(j+1) for j,v in enumerate(P))/ev(P,rr)
    W=[sum(P[j]*(K(1)/(j-i)-nu*rr**(j-i-1))
           for j in range(i+1,4)) for i in range(3)]
    V=invpoly(K,W,P)
    D=nodal(pegs)
    assert len(D)==7
    d=ev(D,rr)
    m=[sum(K(v)/(i+j+1) for i,v in enumerate(D))-nu*d*rr**j for j in (0,1)]
    return V,D,m

def nodal_gate(K,rr,ga,a,s,y,u):
    xx=1-ga;cc=xx-ga*u;dd=xx-2*ga*u
    kk=1+2*u-u*u
    P=p_monic(K,rr)
    ax=[ga*a,ga*s,ga*y,xx,cc,dd]
    V,D,m=p_masks(K,rr,P,ax)
    Lx,Lc=ev(P,xx),ev(P,cc)
    R=[-cc*kk*Lx+xx*Lc,kk*Lx-Lc]
    R0=qr(mul(R,V),P)[1]
    R1=qr(mul(D,[-m[1],m[0]]),P)[1]
    R0+=[K(0)]*(3-len(R0));R1+=[K(0)]*(3-len(R1))
    return [R0[0]*R1[1]-R0[1]*R1[0],R0[0]*R1[2]-R0[2]*R1[0],R0[1]*R1[2]-R0[2]*R1[1]]

def test(front,slot,p,t,verbose=False):
    cases=models(front,slot,False)
    if not cases:return (0,0,0,0)
    G,RR,Old,Phi,Et,Ea,Gh,Th,gQ,ds=projection(front,slot)
    arith,x,c,d=arithmetic_tail()
    counts=[0]*4
    gauss=root_consts(p)
    assert gauss is not None
    for rr in gauss:
        RBase=Bfield(nmod_poly([-rr,1],p),p,t)
        for G0,exS,exU in cases:
            gamma=nmod_poly([int(RBase(q0).x[0]) for q0 in G0],p)
            assert gamma.degree()==len(G0)-1 and gamma.leading_coefficient()==1
            for Mf,e in gamma.factor()[1]:
                E=Bfield(Mf,p,t);gg=E(nmod_poly([0,1],p))
                gc=lambda v:E(int(RBase(v).x[0]))
                gg.inv()
                counts[0]+=1
                SS=ev_poly(Phi,1,E,p,rr,t,gg,E(0)) if exS is None else [qf(c0,gc,gg) for c0 in exS]
                assert len(SS)==(3 if exS is None else len(exS))
                SS[-1].inv()
                S0=gcdp(SS,ev_poly(Old,1,E,p,rr,t,gg,E(0)))
                if len(S0)<=1:continue
                U=Tower(S0);s0=U.gen();g0=U(gg);r1=U(rr)
                counts[1]+=1
                XT=ev_poly(Et,0,U,p,rr,t,g0,s0);XA=ev_poly(Ea,0,U,p,rr,t,g0,s0)
                q5=[v for v in (XT,XA) if len(v)==3]
                if len(XT)==len(XA)==3:
                    q5+= [add(XT,sc(XA,U(i))) for i in range(1,8)]
                for v5 in q5:
                    if len(v5)!=3:continue
                    try:v5[-1].inv()
                    except ArithmeticError:continue
                    break
                else:
                    raise ArithmeticError(('fifth leading',rr,Mf.degree(),len(XT)-1,len(XA)-1))
                Y5=gcdp(gcdp(v5,XT),XA)
                if len(Y5)<=1:continue
                Y=Nested(Y5);y0=Y.gen()
                counts[2]+=1
                A,B,m,ha,hb,active,quiet,H,H4,*_=ds
                DD=ev_poly(arith,1,E,p,rr,t,gg,E(0)) if exU is None else [qf(c0,gc,gg) for c0 in exU]
                assert len(DD)==(4 if exU is None else len(exU))
                DD[-1].inv()
                W=Nested(mon(list(map(lambda v:Y(U(v)),DD))));u=W.gen()
                res=nodal_gate(W,W(Y(r1)),W(Y(g0)),W(Y(U(E(active)))),W(Y(s0)),W(y0),u)
                if verbose:
                    print('shared one-front candidate fifth',front,slot,p,t,rr,Mf.degree(),len(S0)-1,len(Y5)-1,flush=True)
                span_unit(W,*res)
                counts[3]+=1
    return tuple(counts)

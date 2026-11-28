"""Full affine/quartic shared-root live extras through actual fifth and rear."""
from shared_live_fronts import *

@lru_cache(None)
def early5(front,M):
    q,(F,g,X,R,A,B,m,ha,hb,P,H4)=front_model(front,M)
    assert q is not None
    L=literal_fifth(F,A,B,m,ha,hb,q,ev(H4,q),P)
    C,rs=divp(L,list(map(F,nodal([A,B,q]))))
    assert not rs
    print('shared live actual nonhole fifth exact quotient degree',
          front,M.degree(),len(C)-1,flush=True)
    if len(C)!=2:return C,None
    y=-C[0]/C[1]
    print('shared live forced fifth guards',front,y in [A,B,q,X,R],
          'actual ordinary pegs may be used only if fifth weighted',flush=True)
    return C,y

@lru_cache(None)
def exact_gap(front,M,slot):
    s,data=front_model(front,M)
    F,g,X,R,A,B,m,ha,hb,P,H4=data
    _,y=early5(front,M)
    assert y is not None
    u=[F(0),F(1)];k=[F(1),F(2),F(-1)]
    c=[X,F(-1)];d=[X,F(-2)]
    H=[F(-2),F(1),F(4),F(-1)];J=[F(2),F(3),F(-12),F(4)]
    pc,pd,px=subst(P,c),subst(P,d),ev(P,X)
    if slot==8:
        pad=[F(0),F(1)]
        fn=add(mul([F(-2),F(1)],pc),
               sc(add(sc(u,2),mul(k,[F(-2),F(1)])),-px))
    else:
        pad=[F(0),F(0),F(1)]
        fn=sum_poly([mul(H,pd),sc(mul(J,pc),2),sc(mul(k,J),-px)])
    P0,r=divp(fn,pad)
    assert not r and len(P0)==4,(slot,len(P0),r)
    A0=mon(P0)
    if slot in (2,3,4,5):
        z=([A,B,s,y])[slot-2]
        Z0=add(sc(pc,X-z),sc(mul(k,add(c,[-z])),-px))
        B0,rem=divp(Z0,u)
        assert not rem
        A0=gcdp(A0,B0)
        assert A0
    print('shared live exact necessary gap',front,slot,len(A0)-1,flush=True)
    return A0,(F,g,X,R,A,B,s,y,P)

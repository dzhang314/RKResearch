"""Affine reverse numerator, quartic shared-root profile, actual reverse-live ninth site."""
from both_front_active8 import *
from hole_nonzero import exact_factors
from reverse_live_quartic import literal_fifth

@lru_cache(None)
def front_model(front,M):
    F,g,X,R,A,B,m,ha,hb,L,Q,P,H4=model(front,M)
    assert P and len(P)==4 and ev(P,A)==ha and ev(P,B)==hb
    assert R not in [A,B,X] and ev(P,R)
    Y,rest=divp(add(H4,sc(P,-1)),list(map(F,nodal([A,B]))))
    assert not rest
    print('shared live actual fourth exact quotient degree',front,M.degree(),len(Y)-1,flush=True)
    if len(Y)!=2:return None,(F,g,X,R,A,B,m,ha,hb,list(P),list(H4))
    q=-Y[0]/Y[1]
    assert q not in [A,B] and ev(H4,q)==ev(P,q)
    return q,(F,g,X,R,A,B,m,ha,hb,list(P),list(H4))

def star_shape(F,X,P):
    U=[F(0),F(1)]
    k=[F(1),F(2),F(-1)]
    c=[X,F(-1)]
    d=[X-F(2),F(1)]
    F0=sum_poly([mul([F(2),F(-1)],subst(P,c)),
                 sc(mul(U,subst(P,d)),-1),
                 sc(mul(k,[F(-2),F(2)]),ev(P,X))])
    hole=list(map(F,nodal([F(0),F(1),F(2)])))
    Q,R=divp(F0,hole)
    assert not R
    m=X-F(1)
    P3=P[3]
    B0=ev(P,X)+P3+F(3)*P3*m+P[2]
    assert Q==trim([-2*B0])
    return Q

def first_census(front,M):
    q,(F,g,X,R,A,B,m,ha,hb,P,H4)=front_model(front,M)
    if q is None:return ('fourth leading',front)
    H4r=ev(H4,R)
    f5=literal_fifth(F,A,B,m,ha,hb,q,ev(H4,q),[])
    H5r=ev(f5,R)
    u=(X-R)/2
    H8r=4*u**3-12*u**2+3*u+2
    star=star_shape(F,X,P)
    print('shared live early/early-hole/rear pilots',front,M.degree(),
          bool(H4r),bool(H5r),bool(H8r),len(star)-1,q==R,flush=True)
    if not all((H4r,H5r,H8r,star)):
        return ('some exact pivot is zero',front,bool(H4r),bool(H5r),bool(H8r),bool(star))
    H4r.inv();H5r.inv();H8r.inv();star[0].inv()
    print('checked exact field units: physical 4/5/8 hole and ordinary star rear',
          front,M.degree(),flush=True)
    return None

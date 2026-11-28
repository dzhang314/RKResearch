"""A finite-free specialization witness for no transcendental coprime diagonal."""
from coprime_generic_front import *
from shared_one_front_fibers import ev_poly,frac_p
from unequal_finite import Bfield,Tower
from equal_undetected_front import Nested
from extra_active import invpoly
from flint import nmod_poly

@lru_cache(None)
def tail(front,slot,rear):
    Et,Ea,D,q0,q1,guards,ds=setup_front(front,slot)
    xa=1-g;u=y;c=xa-g*u;d=xa-g*(2-u if rear else 2*u)
    q=lambda v:can(g*q0+q1*v)
    k=1+2*u-u*u
    Px,Pc,Pd=map(L,(xa,c,d))
    Qx,Qc,Qd=map(q,(xa,c,d))
    if rear:
        T0=can((2-u)*Pc*Qd*Qx-u*Pd*Qc*Qx+k*(2*u-2)*Px*Qc*Qd)
        T,rem=exdiv(T0,u*(u-1)*(u-2))
    else:
        H=-2+u+4*u*u-u**3;J=4*u**3-12*u*u+3*u+2
        T0=can(H*Pd*Qc*Qx+2*J*Pc*Qd*Qx-k*J*Px*Qc*Qd)
        T,rem=exdiv(T0,u*u)
    assert not rem and T.degrees()[0]==(2 if rear else 5)
    return Et,Ea,D,T,q0,q1,ds

def choose_poly(P,p,t,gg):
    # Univariate s at a concrete gamma value, no Gaussian parameter in this chart.
    a={}
    for (iy,ii,ig,ir,it),v in P.to_dict().items():
        assert iy==ir==0
        a[ii]=(a.get(ii,0)+frac_p(v,p)*pow(gg,ig,p)*pow(t,it,p))%p
    return nmod_poly([a.get(i,0) for i in range(max(a,default=-1)+1)],p)

def remainders(K,g,a,s,y,u,rear,normQ):
    x=1-g; c=x-g*u;d=x-g*(2-u if rear else 2*u);k=1+2*u-u*u
    q=[g*normQ[0],normQ[1]]
    L=mon(list(map(K,Lco)))
    W=[sum(L[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
    WL=invpoly(K,W,L)
    D=nodal([g*a,g*s,g*y,x,c,d])
    A,B=k*ev(L,x)*ev(q,c),ev(L,c)*ev(q,x)
    V=qr(mul(mul([-c*A+x*B,A-B],mul(q,q)),WL),L)[1]
    C=[qr([K(0)]*j+D,L)[1] for j in range(3)]+[V]
    return det([[C[j][i] if i<len(C[j]) else K(0) for j in range(4)] for i in range(4)])

"""Exact arithmetic-rear projection, with a composed resultant witness."""
from regular_star_projection import *
from unequal_finite import Bfield
from unequal_finite import gcdp,add,sc
from flint import nmod_poly

@lru_cache(None)
def arithmetic(front,slot):
    h,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(front)
    x=1-g;u=v;c=x-g*u;d=x-2*g*u
    z={2:a,3:b,4:q}[slot]
    k=1+2*u-u*u;H=-2+u+4*u*u-u**3;J=2+3*u-12*u**2+4*u**3
    Hx,Hc,Hd=map(lambda y:ev(h,y),(x,c,d))
    fu=red(H*Hd+2*J*Hc-k*J*Hx)
    F,R=divmod(fu,u*u);assert not R
    G,R=divmod(red((x-z)*Hc-k*(c-z)*Hx),u);assert not R
    F,fp=remove(red(F),[g,La,Lb]);G,gp=remove(red(G),[g,La,Lb]);assert fp==gp==[1,1,1]
    assert (F.degrees()[0],G.degrees()[0])==(6,4)
    start=perf_counter()
    P0=red(F.resultant(G,0));assert P0
    print('arith exact F/G raw',front,slot,P0.degrees(),round(perf_counter()-start,1),flush=True)
    hd=red(h[-1]);hd0,hh=remove(hd,[g,La,Lb,V])
    guards=[g,La,Lb,V,s-A0,s-B0,x-z,x-a,x-b,x-q,hd0]
    B0,ss=remove(P0,guards);assert B0
    assert B0.degrees()[1:3]==((27 if slot<4 else 33),96)
    assert ss==[14,0,0,0,0,0,0,0,0,0,1]
    print('arith exact F/G guarded',front,slot,B0.degrees(),ss,flush=True)
    early=[a,b,q];early.pop(slot-2)
    E=nodal([*early,x,c,d]);X=W(h);M=[]
    for j in range(4):
        Y=[Z]*j+E;U=W(Y)
        M.append([red(cof(h,U,i)-cof(Y,X,i)) for i in range(1,5)])
    N=det(M)
    print('arith exact N',front,slot,N.degrees(),flush=True)
    return B0,F,G,N,guards

def specialize_g(P,p,tr,g0,iv=0):
    tab={}
    for (i,j,k,l),v0 in P.to_dict().items():
        a=int(v0.p)*pow(int(v0.q),-1,p)%p
        key=(i,j)
        tab[key]=(tab.get(key,0)+a*pow(g0,k,p)*pow(tr,l,p))%p
    return tab

def specialize_s(D,K,s0):
    V={}
    for (i,j),a in D.items():
        V[i]=V.get(i,K(0))+K(a)*s0**j
    return [V.get(i,K(0)) for i in range(max(V,default=-1)+1)]

"""Exact scope and projection shape for a true silent fifth, not an ordinary fifth."""
from rear67_model import model
from regular_star_projection import Co,remove,g,red,v,ev,profile
from functools import lru_cache

@lru_cache(None)
def model5():
    A,B,J,N,S,F,G,H,delta,dat,guards=model()
    a,b,q,La,Lb,A0,B0,x=dat
    c=x-g*v;d=x-2*g*v;k=1+2*v-v*v
    Hx,Hc=map(lambda x:ev(H,x),(x,c))
    # True z=(x Hc-k c Hx)/(Hc-k Hx), u != 0.  In particular
    # z/g = (x L+g k Hx)/(g L), L=(Hc-k Hx)/u.
    L,r=divmod(red(Hc-k*Hx),v);assert not r
    assert L.degrees()[0]==4
    zn=red(x*L+g*k*Hx);zd=red(g*L)
    Gp=Co(G);assert len(Gp)==4
    Z=red(sum(h*zn**j*zd**(3-j) for j,h in enumerate(Gp)))
    pp=profile(True)
    P,counts=remove(Z,[g,pp[-1][3],pp[-1][4],guards['regular_v'],guards['quintic'],
                       guards['terminal_h'],L,zd])
    print('actual silent fifth G-affine degrees',Z.degrees(),P.degrees(),counts,flush=True)
    assert P and P.degrees()[0]>0
    assert (Z.degrees(),P.degrees(),counts)==(
        (12,12,45,0),(12,12,43,0),[2,0,0,0,0,0,0,0])
    return A,B,dict(N=N,S=S,F=F,H=H,delta=delta,dat=dat,
                    guards=guards,Gsilent=P)

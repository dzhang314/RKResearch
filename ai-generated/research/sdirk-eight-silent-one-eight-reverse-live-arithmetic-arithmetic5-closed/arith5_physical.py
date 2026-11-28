"""Actual silent fifth using only the true six ordinary pegs and paid literal fifth."""
from regular_star_projection import *
from arith67_model import model
from arith4_profile import basis
from functools import lru_cache

@lru_cache(None)
def physical():
    A,B,_unused_ord_fifth,N,S,F,G,H,delta,early,gs=model()
    a,b,q,La,Lb,A0,B0,x,c,d,k,h,j=basis()[-1]
    Hx,Hc=ev(H,x),ev(H,c)
    L,r=divmod(red(Hc-k*Hx),v)
    assert not r and L.degrees()[0]==4
    n,den=red(x*L+g*k*Hx),red(g*L)
    p=Co(G,0)
    assert len(p)==4
    J0=red(sum(w*n**i*den**(3-i) for i,w in enumerate(p)))
    J,counts=remove(J0,[g,La,Lb,gs['anchor'],gs['quintic'],gs['terminal_h'],L,den])
    assert (J0.degrees(),J.degrees(),counts)==((12,14,45,1),(12,14,43,1),[2]+[0]*7)
    print('actual arithmetic silent fifth homogeneous',J0.degrees(),J.degrees(),counts,flush=True)
    return A,B,N,S,F,J,gs

if __name__=='__main__':physical()

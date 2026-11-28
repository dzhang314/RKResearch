"""True literal silent fourth: two compact exact projections plus independent rank drop."""
from arith4_profile import basis,pivot
from regular_star_projection import *
from arith3_projection import fivepegs
from small_crt import small_resultant
from functools import lru_cache

@lru_cache(None)
def projection():
    H,J,L,n,d0,guards=pivot()
    a,b,q,La,Lb,A0,B0,x,c,d,k,h,j=basis()[-1]
    j0=Co(J,1)
    J0=red(sum(f*n**i*d0**(3-i) for i,f in enumerate(j0)))
    A,a0=remove(J0,guards)
    assert J0.degrees()==(33,0,47,1)
    assert A.degrees()==(33,0,45,1) and a0==[2]+[0]*(len(guards)-1)
    N0=fivepegs(H,(a,b,x,c,d))
    N,n0=remove(N0,guards)
    assert N0.degrees()==(30,0,48,1)
    assert N.degrees()==(30,0,46,1) and n0==[2]+[0]*(len(guards)-1)
    print('exact silent-fourth compact homogeneous and nodal polynomials',A.degrees(),N.degrees(),
          'guard powers', a0,n0,'outer cap',2868,flush=True)
    return A,N

@lru_cache(None)
def rankdrop():
    P,V,H0,H1,(F0,F1),(a,b,q,La,Lb,A0,B0,x,c,d,k,h,j)=basis()
    R=small_resultant(F0,F1)
    S,ns=remove(R,[g,La,Lb,x-a,x-b])
    assert R.degrees()==(0,0,126,1)
    assert S.degrees()==(0,0,53,1) and ns==[25,6,6,0,0]
    print('exact stage-four zero F₀,F₁ projection',R.degrees(),S.degrees(),ns,flush=True)
    return S

if __name__=='__main__':rankdrop();projection()

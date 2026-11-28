"""Compact ordinary-peg projection before the actual silent fifth gate."""
from arith4_profile import basis,pivot
from arith3_projection import fivepegs,swap
from regular_star_projection import *
from small_crt import small_resultant
from functools import lru_cache

@lru_cache(None)
def projection():
    H,J,L,n,den,guards=pivot()
    a,b,q,La,Lb,A0,B0,x,c,d,*_=basis()[-1]
    # Both a,b and also q are ordinary in this physical placement.
    # The ordinary nodal cannot contain z, the actual silent fifth.
    N0=fivepegs(H,(a,b,x,c,d))
    N,nn=remove(N0,guards)
    assert N.degrees()==(30,0,46,1) and nn==[2]+[0]*(len(guards)-1)
    E=nodal([a,b,q,x,c,d]);WH=W(H)
    rows=[]
    for i in range(3):
        D=[Z]*i+E;WD=W(D)
        rows.append([red(cof(H,WD,j)-cof(D,WH,j)) for j in (2,3,4)])
    Q=det(rows)
    assert Q.degrees()==(22,3,39,1)
    R0=swap(small_resultant(swap(J),swap(Q)))
    R,rr=remove(R0,guards)
    assert R0.degrees()==(83,0,150,1)
    assert R.degrees()==(73,0,130,1)
    assert rr==[6]+[0]*11+[2]+[0]*(len(guards)-13)
    print('actual ordinary fourth minor and compact pivot eliminant',Q.degrees(),
          R0.degrees(),R.degrees(),rr,'u outer cap',7258,flush=True)
    # F1 itself contains a strict-diagonal factor. Its primitive
    # quotient, not the unnormalised F1, is a true nonzero guard here.
    F1,rf=divmod(basis()[4][1],g)
    assert not rf and F1.degrees()==(6,0,11,1)
    U,nu=remove(N,[F1]);V,nv=remove(R,[F1])
    assert (nu,nv,U.degrees(),V.degrees())==([1],[3],(24,0,35,1),(55,0,97,1))
    print('exact true F1 saturation',nu,nv,U.degrees(),V.degrees(),
          'new outer cap',U.degrees()[0]*V.degrees()[2]+U.degrees()[2]*V.degrees()[0],flush=True)
    return U,V

@lru_cache(None)
def pivot_silent_gate():
    from arith_star_model import literal_fifth_poly
    _,_,_,n,d,_=pivot()
    G=Co(literal_fifth_poly(),0)
    assert len(G)==4
    Z0=red(sum(x*n**i*d**(3-i) for i,x in enumerate(G)))
    Z,ns=remove(Z0,[g])
    assert Z0.degrees()==(27,5,45,1) and Z.degrees()==(27,5,43,1) and ns==[2]
    print('actual F1-pivot silently weighted fifth gate',Z.degrees(),ns,flush=True)
    return Z

if __name__=='__main__':projection()

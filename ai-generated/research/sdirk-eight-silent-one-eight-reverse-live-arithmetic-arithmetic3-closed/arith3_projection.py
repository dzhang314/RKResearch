"""Low-degree exact geometric projection retaining the affine shape coordinate."""
from profile_coordinates import coords
from regular_star_projection import *
from small_crt import small_resultant
from functools import lru_cache

def swap(P):
    return C.from_dict({(j,i,k,l):a for (i,j,k,l),a in P.to_dict().items()})

def fivepegs(H,clocks):
    E=nodal(clocks);U=W(H)
    rows=[]
    for i in range(4):
        Q=[Z]*i+E;QW=W(Q)
        rows.append([red(cof(H,QW,j)-cof(Q,U,j)) for j in range(1,5)])
    return det(rows)

@lru_cache(None)
def projection():
    D,F0,F1,G0,G1,J,HH,guards,(a,b,q,x,c,d)=coords()
    # All guards are actual in the nonzero G1 branch, including the
    # degree-five coefficient of the scaled profile and terminal read.
    Q=guards+[G1,HH[-1],ev(HH,x),q-a,q-b,q-x,q-c,q-d,v]
    N0=fivepegs(HH,(a,q,x,c,d))
    N,n=remove(N0,Q)
    assert N.degrees()==(20,4,48,1) and n==[2,0,0,0,1,0,1]+[0]*11
    print('ordinary stage3 nodal',N0.degrees(),N.degrees(),n,flush=True)
    A=swap(small_resultant(swap(J),swap(N)))
    R,k=remove(A,Q)
    assert R.degrees()==(66,0,164,1) and k==[6,0,0,0,3,0,3,0,0,0,2]+[0]*7
    print('exact stage3 fourth eliminant',A.degrees(),R.degrees(),k,
          'outer cap',R.degrees()[0]*D.degrees()[2]+R.degrees()[2]*D.degrees()[0],flush=True)
    return D,R,J,N,Q

@lru_cache(None)
def rankdrop():
    _,F0,F1,G0,G1,_,_,guards,clocks=coords()
    # The eliminant is allowed to retain extra false positive roots.
    U=small_resultant(G0,G1)
    R,n=remove(U,guards[:5])
    assert R.degrees()==(0,0,34,1) and n==[21,4,4,0,5]
    print('stage3 G rank-drop full exact',U.degrees(),R.degrees(),n,flush=True)
    return R

if __name__=='__main__':
    projection();rankdrop()

"""Actual arithmetic-rear ordinary six-peg signed rows with no mass-dependent pivot."""
from functools import lru_cache
from h5_artharth_projection import rear
from h5_arthfront_projection import model
from h567_arithmetic_projection import combine,sc,remove_common
from aq_rear import s as U,g,red,ev
from regular_star_projection import nodal,mul

def I(P,j):
    return red(sum(v/(i+j+1) for i,v in enumerate(P)))

def det2(A,B):
    return combine(mul(A[0],B[1]),sc(-1,mul(A[1],B[0])))

@lru_cache(None)
def shape():
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    F,_,(c,d,k)=rear(2)  # Use only the actual ordinary arithmetic row, common to all z.
    assert F==rear(3)[0]
    E5=nodal([a,b,x,c,d])
    im=[I(E5,i) for i in range(5)]
    m1,m2,m3=[[red(im[j+1]-r*im[j]),red(-g*(im[j]-r*im[j-1]))] for j in (1,2,3)]
    h3,h4=H[-2:]
    assert all(I(H,j)==red(B*r**j) for j in range(4))
    n4,n5=(red(I(H,j)-r*I(H,j-1)) for j in (4,5))
    e5=[E5[-2],-g]
    row3=[sc(-h4,m1),combine([n4],sc(-h4,m2))]
    row2=[combine([n4],sc(-h3,m1),sc(-h4,m2)),
          combine(sc(n4,e5),[n5],sc(-h3,m2),sc(-h4,m3))]
    # The two fixed tail gaps remove one exact -(gamma*u)^2 from the terminal row.
    Mc=sc((c-a)*(c-b)*ev(H,c),[c,-g])
    Mx=sc(2*(x-a)*(x-b)*ev(H,x),[x,-g])
    terminal=[combine(sc(c**j,Mc),sc(x**j,Mx)) for j in range(2)]
    C,ce=remove_common(det2(row3,row2),gs)
    T,te=remove_common(det2(row3,terminal),gs)
    N,ne=remove_common(det2(row2,terminal),gs)
    print('actual arithmetic middle mass-free shapes',ce,te,ne,
          [[c.degrees() for c in W] for W in (C,T,N)],flush=True)
    return C,T,N,F,(c,d,k)

if __name__=='__main__':shape()

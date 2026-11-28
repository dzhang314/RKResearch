"""True arithmetic front with actual silent eighth: a mass-free quadratic cofactor."""
from functools import lru_cache
from h5_arthfront_projection import model
from h58_star_projection import arrdet
from h567_arithmetic_projection import combine,sc,remove_common
from h567_af_ar_shape import I
from aq_rear import s as U,g,red,ev,divide
from regular_star_projection import nodal,Co,Z

@lru_cache(None)
def shape():
    H,D,A,B,J,Z0,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    u=U;c=x-g*u;k=1+2*u-u**2
    z=x+g*k*(u-2)/2
    ph=2*u+k*(u-2)
    F=divide(red((u-2)*ev(H,c)-ph*ev(H,x)),u)
    h3,h4=H[-2:]
    assert F.degrees()[1]==4 and Co(F,1)[-1]==h4*g**4
    E4=nodal([a,b,c,x])
    hr=ev(H,r)
    assert hr==g*gs[4] and all(I(H,j)==red(B*r**j) for j in range(4))
    im=[I(E4,i) for i in range(6)]
    m1,m2,m3,m4=[[red(im[j+1]-r*im[j]),red(-g*(im[j]-r*im[j-1]))] for j in range(1,5)]
    e4=[E4[-2],-g]
    n4,n5=(red(I(H,j)-r*I(H,j-1)) for j in (4,5))
    Er=ev(E4,r)
    L=[red(hr*im[i]-B*r**i*Er) for i in range(6)]
    row0=[[L[j+1],red(-g*L[j])] for j in range(3)]
    row3=[sc(-h4,m1),sc(-h4,m2),combine([n4],sc(-h4,m3))]
    row2=[combine(sc(-h3,m1),sc(-h4,m2)),
          combine([n4],sc(-h3,m2),sc(-h4,m3)),
          combine(sc(n4,e4),[n5],sc(-h3,m3),sc(-h4,m4))]
    Mc=sc((c-a)*(c-b),[c,-g]);Mx=sc((x-a)*(x-b),[x,-g])
    terminal=[combine(sc(ph*c**j,Mc),sc((u-2)*x**j,Mx)) for j in range(3)]
    out=[];guards=[]
    for mm in ([row0,row3,row2],[row0,row3,terminal],[row0,row2,terminal],[row3,row2,terminal]):
        Q,e=remove_common(arrdet(mm),gs)
        out.append(Q)
        guards.append(e)
    print('silent8 arithmetic front mass-free true four minors',
          guards,[[a.degrees() for a in Q] for Q in out],flush=True)
    return tuple(out),F,(c,x,z,k,ph)

if __name__=='__main__':shape()

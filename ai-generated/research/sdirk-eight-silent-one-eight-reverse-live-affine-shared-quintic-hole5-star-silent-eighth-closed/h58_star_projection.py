"""Regular corrected ordinary fifth hole and actual ordinarily silent eighth."""
from functools import lru_cache
from h5_star_branches import L,SC,specialize,main_front
from h5_regular_projection import model,gpoly
from h54_arithmetic_projection import remove_in_cubic,Yrem
from h567_star_projection import sig_mom
from h567_arithmetic_projection import combine,sc,remove_common
from aq_rear import u as Y,s as U,g,red,ev,divide
from regular_star_projection import Z,Co,remove,nodal,mul
from hole4_projection import crt
from aq5_projection import flip
from itertools import permutations

def arrdet(M):
    n=len(M)
    out=[]
    for b in permutations(range(n)):
        x=[Z+1]
        for i,j in enumerate(b):x=mul(x,M[i][j])
        x=sc((-1)**sum(b[i]>b[j] for j in range(n) for i in range(j)),x)
        out.append(x)
    return combine(*out)

@lru_cache(None)
def signed_model():
    H,D,A,B,J,Z0,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    u=U;k=1+2*u-u**2;c=x-g*u
    ph=2*u+k*(u-2)
    F=divide(red((u-2)*ev(H,c)-ph*ev(H,x)),u)
    h3,h4=H[-2:]
    assert F.degrees()[1]==4
    z=x+g*k*(u-2)/2
    hr=ev(H,r)
    assert hr==g*gs[4]
    nu4,nu5=(sig_mom(H,i,hr,B,r) for i in (4,5))
    assert all(not sig_mom(H,i,hr,B,r) for i in range(4))
    E4=nodal([a,b,x,c])
    im=[sig_mom(E4,i,hr,B,r) for i in range(6)]
    m0,m1,m2,m3,m4=[[im[i+1],red(-g*im[i])] for i in range(5)]
    e4=[E4[-2],-g]
    row0=[m0,m1,m2]
    row1=[sc(h4,m1),sc(h4,m2),combine(sc(h4,m3),[-nu4])]
    row2=[sc(h4*h4,m2),combine(sc(h4*h4,m3),[-h4*nu4]),
          combine(sc(h4*h4,m4),sc(-h4*nu4,e4),[-h4*nu5+h3*nu4])]
    Mc=sc((c-a)*(c-b),[c,-g]);Mx=sc((x-a)*(x-b),[x,-g])
    term=[combine(sc(ph*c**j,Mc),sc((u-2)*x**j,Mx)) for j in range(3)]
    C0,ce=remove_common(arrdet([row0,row1,row2]),gs)
    N0,ne=remove_common(arrdet([row0,row1,term]),gs)
    assert ce==[3,1,1,0,2,0,0,0] and ne==[2,0,0,0,1,0,0,0]
    assert len(C0)==len(N0)==4
    assert [v.degrees()[1] for v in C0]==[3]*4
    print('silent8 two normalized signed gates',ce,ne,[[v.degrees() for v in p] for p in (C0,N0)],flush=True)
    return C0,N0,F,(c,x,z,k,ph)

def res23_terms(P,Q):
    a,b,c=P
    e,f,y,h=Q
    terms=(a**3*h**2, -a**2*b*y*h, -2*a**2*c*f*h, a**2*c*y*y,
           a*b*b*f*h,3*a*b*c*e*h,-a*b*c*f*y,-2*a*c*c*e*y,
           a*c*c*f*f,-b**3*e*h,b*b*c*e*y,-b*c*c*e*f,c**3*e*e)
    return terms

def res23(P,Q):
    return Yrem(sum(map(Yrem,res23_terms(P,Q))))

@lru_cache(None)
def project(cubic):
    H,D,A,B,J,Z0,gs,dat=model(True)
    C0,N0,F,_=signed_model()
    T=C0
    if cubic:
        P=SC
        F=Yrem(F)
        raw=res23(list(map(Yrem,Co(J,1))),list(map(Yrem,T)))
    else:
        P=main_front()
        raw=red(ev(T,(2*Y+1)/3))
    V,e0=remove(raw,gs)
    Q=flip(crt(flip(F),flip(V),'true silent8 gap'))
    if cubic:Q=Yrem(Q)
    Q0,qe=remove(Q,gs)
    if cubic:
        Q0,pa=remove_in_cubic(Q0,A)
        Q0,ph=remove_in_cubic(Q0,gs[4])
        Q0,pr=remove_in_cubic(Q0,gs[1])
        assert raw.degrees()==(2,6,84,1)
        assert e0==[6,0,0,0,0,0,0,0] and qe==[12,0,0,0,0,0,0,0]
        assert Q.degrees()==(2,0,372,0) and Q0.degrees()==(2,0,210,1)
        assert (pa,ph,pr)==(7,4,8)
    else:
        pa=ph=pr=0
        assert e0==[0,0,0,0,0,0,0,0] and qe==[6,0,2,0,0,3,0,0]
        assert Q.degrees()==(61,0,138,1) and Q0.degrees()==(46,0,90,0)
    print('true silent8 gap projection',cubic,'raw gate',raw.degrees(),V.degrees(),e0,'Q exact',Q.degrees(),'Q guards',Q0.degrees(),qe,pa,ph,pr,flush=True)
    R=crt(P,Q0,'true silent8 diagonal')
    R0,e=remove(R,tuple(v for v in gs if v.degrees()[0]==0))
    T,d=remove(R0,(L,))
    print('true silent8 outer projection',cubic,'exact',R.degrees(),'guarded',R0.degrees(),e,'non L',T.degrees(),d,flush=True)
    if cubic:
        assert R.degrees()[2]==R0.degrees()[2]==630
        assert e==[0,0,0,0] and d==[0]
        return ((gpoly(R0).monic(),P,Q0,'usual'),)
    assert (R.degrees()[2],R0.degrees()[2],T.degrees()[2])==(744,504,492)
    assert e==[168,18,0,0] and d==[4]
    PL,QL=specialize(P),specialize(Q0)
    assert PL.degrees()==(4,0,2,1) and QL.degrees()==(42,0,2,0)
    print('true silent8 specialized degrees',PL.degrees(),QL.degrees(),flush=True)
    return ((gpoly(T).monic(),P,Q0,'usual'),(gpoly(L).monic(),PL,QL,'degenerate'))

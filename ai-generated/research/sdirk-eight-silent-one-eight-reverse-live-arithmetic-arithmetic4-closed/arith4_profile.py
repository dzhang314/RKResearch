"""True arithmetic-front/ordinary-arithmetic-rear, actual physical fourth silent."""
from regular_star_projection import *
from profile_coordinates import coords
from star4_actual_fifth import common_division
from functools import lru_cache

@lru_cache(None)
def basis():
    H,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(False)
    A,B,m=map(lambda w:cv(F2,w),ends(False,1))
    ha,hb=map(cast,((A-1)/2,(B-1-m)/2))
    Ga,Gb=ev(L3,a),ev(L3,b)
    H0=mul(list(map(C.constant,L4)),[red(ha*Lb*b-hb*La*a),red(hb*La-ha*Lb)])
    H0=H0+[Z]*(6-len(H0))
    U=mul(list(map(C.constant,L4)),[red(Ga*Lb*b-Gb*La*a),red(Gb*La-Ga*Lb)])
    H1=[red(D*(L3[i] if i<len(L3) else 0)-z) for i,z in enumerate(U)]
    assert all(red(V*e+P*f)==h for e,f,h in zip(H0,H1,H))
    assert ev(H0,b)==red(D*hb) and ev(H0,a)==red(D*ha)
    assert not ev(H1,b) and not ev(H1,a)
    u=v;x=1-g;c=x-g*u;d=x-2*g*u
    k=1+2*u-u*u;h=-2+u+4*u*u-u**3;j=2+3*u-12*u*u+4*u**3
    Fs=[]
    for T in (H0,H1):
        X,Y,Z0=map(lambda x0:ev(T,x0),(x,c,d))
        F,R=divmod(red(h*Z0+2*j*Y-k*j*X),u*u)
        assert not R
        Fs.append(red(F))
    assert Fs==list(coords()[1:3]) # Same literal arithmetic suffix and early basis.
    return P,V,H0,H1,Fs,(a,b,q,La,Lb,A0,B0,x,c,d,k,h,j)

@lru_cache(None)
def pivot():
    P,V,H0,H1,(F0,F1),(a,b,q,La,Lb,A0,B0,x,c,d,k,h,j)=basis()
    u=v
    gs=[g,La,Lb,x-a,x-b,c-a,c-b,d-a,d-b,u,k]
    HH,hs=common_division([red(F1*a-F0*b) for a,b in zip(H0,H1)],gs)
    J,nj=remove(red(F1*P+F0*V),gs)
    assert J.degrees()==(6,3,11,1) and hs==nj==[1,1,1]+[0]*8
    print('F-pivot profile degrees and guards', [z.degrees() for z in HH],hs,
          'actual fourth in s',J.degrees(),nj,flush=True)
    Hx,Hc,Hd=map(lambda y:ev(HH,y),(x,c,d))
    L,r=divmod(red(Hc-k*Hx),u)
    assert not r
    sd,sn=red(g*L),red(x*L+g*k*Hx)
    [sd,sn],ln=common_division([sd,sn],gs+[HH[-1],Hx,Hc,Hd,F1])
    assert sd.degrees()==sn.degrees()==(9,0,12,1) and ln==[1]+[0]*15
    print('actual z as s amplitude',L.degrees(),sd.degrees(),sn.degrees(),ln,flush=True)
    guards=gs+[F1,HH[-1],Hx,Hc,Hd,L,sd,
          red(sn-A0*sd),red(sn-B0*sd),red(g*sn-x*sd),red(g*sn-c*sd),red(g*sn-d*sd)]
    return HH,J,L,sn,sd,guards

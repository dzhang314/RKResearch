"""Scope: arithmetic physical third silent; free profile coordinate before fourth."""
from regular_star_projection import *
from functools import lru_cache

@lru_cache(None)
def coords():
    H,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(False)
    A0,B0,m=map(lambda w:cv(F2,w),ends(False,1))
    ha,hb=(A0-1)/2,(B0-1-m)/2
    ha,hb=map(cast,(ha,hb))
    Ga,Gb=ev(L3,a),ev(L3,b)
    H0=mul(list(map(C.constant,L4)),[red(ha*Lb*b-hb*La*a),red(hb*La-ha*Lb)])
    H0=H0+[Z]*(6-len(H0))
    U=mul(list(map(C.constant,L4)),[red(Ga*Lb*b-Gb*La*a),red(Gb*La-Ga*Lb)])
    H1=[red(D*(L3[i] if i<len(L3) else 0)-z) for i,z in enumerate(U)]
    assert all(red(V*e+P*f)==h for e,f,h in zip(H0,H1,H))
    assert ev(H0,b)==red(D*hb) and ev(H0,a)==red(D*ha)
    assert not ev(H1,a) and not ev(H1,b)
    u=v; x=1-g;c=x-g*u;d=x-2*g*u
    z=b;k=1+2*u-u*u;h=-2+u+4*u*u-u**3;j=2+3*u-12*u*u+4*u**3
    Fs=[];Gs=[]
    for T in (H0,H1):
        Hx,Hc,Hd=map(lambda y:ev(T,y),(x,c,d))
        F,R=divmod(red(h*Hd+2*j*Hc-k*j*Hx),u*u)
        G,S=divmod(red((x-z)*Hc-k*(c-z)*Hx),u)
        assert not R and not S
        Fs.append(red(F));Gs.append(red(G))
    F0,F1=Fs;G0,G1=Gs
    Z0=red(F0*G1-F1*G0)
    egs=[g,La,Lb,x-a,x-b,c-a,c-b,d-a,d-b]
    Z0,fac=remove(Z0,egs)
    assert Z0.degrees()==(9,0,12,1) and fac==[2,1,1,0,0,0,0,0,0]
    print('profile coefficient shape', [L.degrees() for L in (*Fs,*Gs,Z0)],'det guard factors',fac,flush=True)
    HH=[red(G1*a0-G0*a1) for a0,a1 in zip(H0,H1)]
    from star4_actual_fifth import common_division
    HH,facs=common_division(HH,egs)
    assert facs==[1,1,1,0,0,0,0,0,0]
    print('G-pivot homogeneous profile', [h.degrees() for h in HH],facs,flush=True)
    J,facj=remove(red(G1*P+G0*V),egs)
    assert J.degrees()==(4,3,12,1) and facj==[1,1,1,0,0,0,0,0,0]
    print('G-pivot exact fourth',J.degrees(),facj,flush=True)
    return (Z0,F0,F1,G0,G1,J,HH,egs,(a,b,q,x,c,d))

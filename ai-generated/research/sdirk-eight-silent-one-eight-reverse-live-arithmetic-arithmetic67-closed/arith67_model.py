"""Genuine physical 6 or 7 silence, arithmetic front, ordinary arithmetic rear."""
from arith_silent8_crt import model as fifth_template
from regular_star_projection import Co,profile,red,remove,ev,v,s,t,g,con
from small_crt import small_resultant
from functools import lru_cache
from time import perf_counter

@lru_cache(None)
def model():
    # Reuse only the four-peg missing quartic N and ordinary fifth formulas.
    # No ordinary-silent-eighth tail equation is used.
    _,J,_,N,G,H,d0,dat=fifth_template()
    H0,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(False)
    R=Co(N,0);assert len(R)==5
    S=red(sum((2**j-1)*R[j]*v**(j-1) for j in range(1,5)))
    T=red(sum((2-2**j)*r*v**j for j,r in enumerate(R)))
    assert S.degrees()[0]==3 and T.degrees()[0]==4
    assert not red(ev(R,2*v)-N-v*S) and not red(N-T-v*S)
    x=1-g;c=x-g*v;d=x-2*g*v
    k=1+2*v-v*v;h=-2+v+4*v*v-v**3;j=2+3*v-12*v*v+4*v**3
    Hx,Hc,Hd=map(lambda x0:ev(H0,x0),(x,c,d))
    F,r=divmod(red(h*Hd+2*j*Hc-k*j*Hx),v*v);assert not r
    V0,_=remove(V,[g,La,Lb])
    hh,_=remove(H0[-1],[g,La,Lb,V0])
    hx,_=remove(Hx,[g,La,Lb,V0])
    F,first=remove(red(F),[g,La,Lb,V0])
    assert (F.degrees(),first)==((6,3,11,1),[1,1,1,0])
    ls=[g,La,Lb,V0,s-A0,s-B0,x-a,x-b,x-q,hh,hx,R[4],R[0]]
    A=small_resultant(S,T);A1,ca=remove(A,ls)
    R4,rx=remove(R[4],[g,hh])
    print('arith both front first exact pair',A.degrees(),A1.degrees(),ca,
          'true lead',R4.degrees(),rx,flush=True)
    assert (A.degrees(),A1.degrees())==((0,55,168,1),(0,53,146,1))
    assert ca==[16,0,0,0,0,0,0,0,0,1,0,0,0]
    assert R4.degrees()==(0,5,14,1) and rx==[4,1]
    P0,cp=remove(A1,[R4])
    assert cp==[1] and P0.degrees()==(0,48,132,1)
    B=small_resultant(S,F);P1,fb=remove(B,ls)
    assert (B.degrees(),P1.degrees())==((0,56,177,1),(0,54,156,1))
    assert fb==[15,0,0,0,0,0,0,0,0,1,0,0,0]
    assert J.degrees()==(0,32,69,1)
    early=dat[5:8]
    assert not red((1+6*t)*(1-6*t)+17)
    print('actual arithmetic front/rear compact exact',
           P0.degrees(),P1.degrees(),J.degrees(),
           'ordinary fifth invariant check',J==con(J),J==-con(J),flush=True)
    gg={'gamma':g,'early_a':La,'early_b':Lb,'anchor':V0,'quintic':hh,'terminal_h':hx,
        'nodal_lead':R[4],'nodal_at_terminal':R[0],'terminal_a':x-a,
        'terminal_b':x-b,'terminal_q':x-q,'literal_fourth':red((s-A0)*(s-B0))}
    return P0,P1,J,N,S,F,G,H,d0,early,gg

if __name__=='__main__':model()

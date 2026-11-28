"""True regular ordinary-arithmetic rear, star front, silent physical 6 or 7."""
from functools import lru_cache
from regular_star_projection import Co,ev,profile,red,remove,v,s,g
from small_crt import small_resultant
from silent8_diag import primitive,get_inputs
from silent8_star_fifth import model as ordinary_fifth_model,literal_fifth_poly

@lru_cache(None)
def model():
    W,_,N,L,delta,dat=ordinary_fifth_model()
    H,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(True)
    R=Co(N)
    x=1-g;c=x-g*v;d=x-2*g*v
    k=1+2*v-v*v;h=-2+v+4*v*v-v**3;j=2+3*v-12*v*v+4*v**3
    # R(2v)-R(v)=v*S, 2R(v)-R(2v)=T.
    S=red(sum((2**j-1)*R[j]*v**(j-1) for j in range(1,5)))
    T=red(sum((2-2**j)*r*v**j for j,r in enumerate(R)))
    assert S.degrees()[0]==3 and T.degrees()[0]==4
    assert not red(ev(R,2*v)-N-v*S) and not red(N-T-v*S)
    Hx,Hc,Hd=map(lambda x0:ev(H,x0),(x,c,d))
    F,rem=divmod(red(h*Hd+2*j*Hc-k*j*Hx),v*v);assert not rem
    V0,_=remove(V,[g,La,Lb])
    hh,_=remove(H[-1],[g,La,Lb,V0])
    hx,_=remove(Hx,[g,La,Lb,V0])
    F,fs=remove(red(F),[g,La,Lb,V0]); assert (F.degrees(),fs)==((6,3,11,0),[1,1,1,0])
    ls=[g,La,Lb,V0,s-A0,s-B0,x-a,x-b,x-q,hh,hx,R[4],R[0]]
    G0=small_resultant(S,T)
    A,ga=remove(G0,ls)
    assert (G0.degrees(),A.degrees())==((0,55,168,0),(0,53,146,0))
    assert ga==[16,0,0,0,0,0,0,0,0,1,0,0,0]
    R4,rr=remove(R[4],[s-A0,s-B0,x-a,x-b,x-q])
    assert rr==[0]*5
    # Normalize the true quartic leading coefficient as in the pivot proof.
    U,zu=primitive(R4); assert zu==4
    C=U.factor(); print('quartic leading factors',[(B.degrees(),e) for B,e in C[1]],flush=True)
    I,_=primitive(A)
    D0=next(B for B,e in I.factor()[1] if B.degrees()==(14,5))
    assert not U%D0              # Actual R[4] != 0 therefore D0 != 0.
    PA,rem=divmod(I,D0);assert not rem and PA.degrees()==(132,48)

    F0=small_resultant(S,F)
    B,gb=remove(F0,ls)
    assert (F0.degrees(),B.degrees())==((0,56,177,0),(0,54,156,0))
    assert gb==[15,0,0,0,0,0,0,0,0,1,0,0,0]
    PB,zb=primitive(B);assert not zb
    _,J=get_inputs()
    _,G,_=literal_fifth_poly()
    print('true arithmetic rear projection inputs',PA.degrees(),PB.degrees(),
          {j:Q.degrees() for j,Q in J.items()},flush=True)
    guards={'gamma':g,'regular_v':V0,'quintic':hh,'terminal_h':hx,
       'nodal_lead':R[4],'terminal_q':x-q,
       'fourth_front':red((s-A0)*(s-B0)),
       'terminal_front':red((x-a)*(x-b)),'early_gauss':red(La*Lb),
       'nodal_at_terminal':R[0]}
    return PA,PB,J,N,S,F,G,L,delta,dat,guards

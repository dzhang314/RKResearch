"""Small exact Sylvester matrices over Q(t)[s, gamma]."""
from regular_star_projection import *
from functools import lru_cache
from time import perf_counter
from small_crt import small_resultant

@lru_cache(None)
def arith_silent8_system():
    h,P,V,den,(a,b,q,La,Lb,A0,B0)=profile(False)
    x=1-g;u=v;c=x-g*u
    k=1+2*u-u*u;J=2*u+k*(u-2)
    Hx,Hc=map(lambda y:ev(h,y),(x,c))
    R,rem=divmod(red((u-2)*Hc-J*Hx),u);assert not rem
    F=red(R);assert F.degrees()[0]==5
    E=nodal([a,b,q,x,c]);X=W(h);M=[]
    for j in range(4):
        Y=[Z]*j+E;U=W(Y)
        M.append([red(cof(h,U,i)-cof(Y,X,i)) for i in range(1,5)])
    N=det(M);assert N.degrees()[0]==4
    V0,_=remove(V,[g,La,Lb])
    F,SF=remove(F,[g,La,Lb,V0]);N,SN=remove(N,[g,La,Lb,V0])
    assert SF==[1,1,1,0] and SN==[6,4,4,2]
    now=perf_counter()
    D=small_resultant(F,N);assert D.degrees()==(0,50,164,1)
    print('fixed small Sylvester F,N',D.degrees(),round(perf_counter()-now,2),flush=True)
    h5,_=remove(h[-1],[g,La,Lb,V0]);hx,_=remove(Hx,[g,La,Lb,V0])
    D0,ss=remove(D,[g,La,Lb,V0,s-A0,s-B0,x-a,x-b,x-q,h5,hx])
    assert D0.degrees()==(0,32,90,1) and ss==[12,0,0,0,0,0,0,0,0,3,4]
    return D0,F,N

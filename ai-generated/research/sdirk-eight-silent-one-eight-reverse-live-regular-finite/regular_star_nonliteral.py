"""Regular star roof with six ordinary pegs and no fixed extra root."""
from regular_star_projection import *
from itertools import combinations

@lru_cache(None)
def get_nonliteral(front):
    h,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(front)
    x=1-g;c=x-g-g*v;d=x-g+g*v;k=2-v*v
    Hx,Hc,Hd=map(lambda y:ev(h,y),(x,c,d))
    S,rem=divmod(red((1-v)*Hc-(1+v)*Hd+2*v*k*Hx),v*(v*v-1));assert not rem
    A,B=centered(red(S))
    E=nodal([a,b,q,x,c,d]);X=W(h)
    M=[]
    for j in range(3):
        Y=[Z]*j+E;U=W(Y)
        M.append([red(cof(h,U,i)-cof(Y,X,i)) for i in range(1,5)])
    J=[]
    h5,_=remove(h[-1],[g,La,Lb,V])
    hx,_=remove(Hx,[g,La,Lb,V])
    V0,vg=remove(V,[g,La,Lb]);assert vg==[2,0,0]
    guards=[g,La,Lb,V0,s-A0,s-B0,x-a,x-b,x-q,h5,hx]
    for II in combinations(range(4),3):
        N=centered(det([[M[j][i] for i in II] for j in range(3)]));assert len(N)==4
        H=red(sum(P0*(-A)**j*B**(3-j) for j,P0 in enumerate(N)))
        U,ss=remove(H,guards);assert U and ss[3]==1
        print('regular nonliteral star exact',front,II,H.degrees(),U.degrees(),ss,flush=True)
        J.append(U)
    assert [h.degrees()[1:3] for h in J]==[(18,55),(17,54),(16,54),(16,54)]
    return J,A,B

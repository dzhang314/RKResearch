"""Regular nonliteral ordinary-eighth arithmetic rear with six pegs."""
from regular_arith_projection import *
from itertools import combinations
from flint import nmod_mpoly_ctx

@lru_cache(None)
def nonliteral_arithmetic(front):
    h,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(front)
    x=1-g;u=v;c=x-g*u;d=x-2*g*u
    k=1+2*u-u*u;H=-2+u+4*u*u-u**3;J=2+3*u-12*u**2+4*u**3
    Hx,Hc,Hd=map(lambda y:ev(h,y),(x,c,d))
    ff,rem=divmod(red(H*Hd+2*J*Hc-k*J*Hx),u*u);assert not rem
    V0,_=remove(V,[g,La,Lb])
    F,r0=remove(red(ff),[g,La,Lb,V0]);assert F.degrees()[0]==6
    h5,_=remove(h[-1],[g,La,Lb,V0]);hx,_=remove(Hx,[g,La,Lb,V0])
    guards=[g,La,Lb,V0,s-A0,s-B0,x-a,x-b,x-q,h5,hx]
    E=nodal([a,b,q,x,c,d]);X=W(h)
    M=[]
    for j in range(3):
        Y=[Z]*j+E;U=W(Y)
        M.append([red(cof(h,U,i)-cof(Y,X,i)) for i in range(1,5)])
    N=[]
    for J in combinations(range(4),3):
        P0=det([[M[j][i] for i in J] for j in range(3)])
        P1,r=remove(P0,guards)
        assert r[3]==1
        N.append(P1)
        print('arith nonliteral exact minor',front,J,P0.degrees(),P1.degrees(),r,flush=True)
    assert F.degrees()[:3]==(6,3,11) and N[0].degrees()[:3]==(6,9,28)
    return F,N

def resultant_sample(F,N,p,t0,g0):
    # The exact symbolic Sylvester resultant is defined over Q(t)[g,s].
    # Its s-degree cap is 6*3+6*9=72. This degree is attained by one
    # full-degree specialization, so whole coefficient fibers are retained.
    C0=nmod_mpoly_ctx.get(['u','s'],p)
    A,B=[C0.from_dict(specialize_g(X,p,t0,g0)) for X in (F,N)]
    assert A.degrees()[0]==B.degrees()[0]==6
    M=A.resultant(B,0)
    D={}
    for (i,j),a in M.to_dict().items():
        assert i==0
        D[j]=int(a)
    S=nmod_poly([D.get(k,0) for k in range(max(D,default=-1)+1)],p)
    assert S.degree()==72
    return S

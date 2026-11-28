"""Fresh exact representative: actual physical second ordinarily silent."""
from regular_star_projection import *
from star4_actual_fifth import common_division
from small_crt import small_resultant
from time import perf_counter
from functools import lru_cache
from flint import nmod_mpoly_ctx

@lru_cache(None)
def model():
    H,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(False)
    x=1-g;u=v;c=x-g*u;d=x-2*g*u;z=a
    k=1+2*u-u*u;h=-2+u+4*u*u-u**3;j=2+3*u-12*u*u+4*u**3
    Hx,Hc,Hd=map(lambda y:ev(H,y),(x,c,d))
    F,rf=divmod(red(h*Hd+2*j*Hc-k*j*Hx),u*u)
    G,rg=divmod(red((x-z)*Hc-k*(c-z)*Hx),u)
    assert not rf and not rg
    F,fp=remove(red(F),[g,La,Lb]);G,gp=remove(red(G),[g,La,Lb])
    assert fp==gp==[1,1,1] and F.degrees()[0]==6 and G.degrees()[0]==4
    hl,_=remove(H[-1],[g,La,Lb,V])
    V0,_=remove(V,[g,La,Lb])
    HX,_=remove(Hx,[g,La,Lb,V0])
    guards=[g,La,Lb,V0,s-A0,s-B0,x-z,x-b,x-q,hl,HX]
    E=nodal([b,q,x])
    U=W(H)
    # H*E3 belongs to the exact homogeneous zero-read kernel.
    HE=mul(H,E)
    assert W(HE)==mul(E,U)
    cols=[]
    for e in range(5):
        P0=[Z]*e+E;T=W(P0)
        cols.append([red(cof(H,T,i)-cof(P0,U,i)) for i in range(1,5)])
    R=[(-1)**e*det([C for i,C in enumerate(cols) if i!=e]) for e in range(5)]
    init=[r.degrees() for r in R]
    R,rr=common_division(R,guards)
    assert rr==[5,4,4,1,0,0,0,0,0,1,0]
    print('3-peg cofactor family',init,[r.degrees() for r in R],rr,flush=True)
    Rc,Rd=ev(R,c),ev(R,d)
    PC0,r=divmod(red(h*(c-z)*Rd+j*(d-z)*Rc),u);assert not r
    PC,cc=remove(red(PC0),guards)
    Cross,r=divmod(red(Rc*Hd-Rd*Hc),u);assert not r
    Cross,xc=remove(red(Cross),guards)
    assert cc==[0]*11 and xc==[2,1,1,0,0,0,0,0,0,0,0]
    print('paid ratio nodal gates',PC.degrees(),cc,Cross.degrees(),xc,flush=True)
    # Independent raw 5-peg determinant for correctness and shape comparison.
    EE=nodal([b,q,x,c,d])
    mat=[]
    for h0 in range(4):
        P0=[Z]*h0+EE;T=W(P0)
        mat.append([red(cof(H,T,i)-cof(P0,U,i)) for i in range(1,5)])
    N0=det(mat)
    N,nn=remove(N0,guards)
    assert nn==[5,4,4,1,0,0,0,0,0,0,0]
    print('ordinary five-peg determinant',N0.degrees(),N.degrees(),nn,flush=True)
    return F,G,PC,Cross,N,guards,H,R,(a,b,q,x,c,d,z),HE

def cast3(X,p,t):
    K=nmod_mpoly_ctx.get(['v','s','g'],p);J={}
    for (i,j,k,l),v0 in X.to_dict().items():
        t0=int(v0.p)*pow(int(v0.q),-1,p)*pow(t,l,p)
        J[i,j,k]=(J.get((i,j,k),0)+t0)%p
    return K.from_dict(J)

def sizes(p=1129,t=203):
    F,G,D,E,N,Q,*_=model()
    L=[cast3(K,p,t) for K in (F,G,D,E,N)+tuple(Q)]
    F,G,D,E,N,*V=L
    for name,A,B in [('FG',F,G),('GP',G,D),('FP',F,D),('GN',G,N),
                     ('FN',F,N),('GC',G,E)]:
        t0=perf_counter()
        M=A.resultant(B,0)
        ks=[]
        for W in V:
            k=0
            while M and any(W.degrees()):
                T,R=divmod(M,W)
                if R:break
                M=T;k+=1
            ks.append(k)
        print('oriented modular proposal shape only',name,M.degrees(),ks,
               round(perf_counter()-t0,3),flush=True)

if __name__=='__main__':sizes()

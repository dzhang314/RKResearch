"""Exact regular literal-silent star tail and Padé resultant projections."""
from mixed_front_projection import front_projection,L3,L4,L5
from seven_k0_anchors import ends,h4,pol,F2,cv
from flint import fmpq_mpoly_ctx,fmpq,nmod_poly
from sympy import isprime
from itertools import permutations
from functools import lru_cache
from time import perf_counter

C=fmpq_mpoly_ctx.get(['v','s','g','t'])
v,s,g,t=C.gens();O=C.constant(1);Z=C.constant(0)
TT=t*t-fmpq(1,2)
def red(P):return divmod(P,TT)[1] if hasattr(P,'to_dict') else C.constant(P)
def con(P):return C.from_dict({I:d*(-1)**I[-1] for I,d in P.to_dict().items()})
def left(P):return C.from_dict({(0,*I):d for I,d in P.to_dict().items()})
def cast(x):
    u=F2(x).v
    return u.a[0]+u.b[0]*t
def ev(h,y):return red(sum(a*y**j for j,a in enumerate(h)))
def Co(P,var=0):
    J={}
    for I,d in P.to_dict().items():
        jj=list(I);jj[var]=0
        J.setdefault(I[var],{})[tuple(jj)]=d
    return [C.from_dict(J.get(k,{})) for k in range(max(J,default=-1)+1)]
def centered(P):
    Q=Co(P);assert all(not Q[i] for i in range(1,len(Q),2))
    return Q[::2]
def trim(a):
    n=len(a)
    while n and not a[n-1]:n-=1
    return a[:n]
def mul(a,b):
    y=[Z]*(len(a)+len(b)-1)
    for i,z in enumerate(a):
        for j,w in enumerate(b):y[i+j]+=z*w
    return trim([red(x) for x in y])
def nodal(p):
    q=[O]
    for z in p:q=mul(q,[-z,O])
    return q
def W(q):return [red(sum(q[j]/(j-i) for j in range(i+1,len(q)))) for i in range(len(q)-1)]
def cof(q,r,n):
    return red(sum(a*r[n-i] for i,a in enumerate(q) if 0<=n-i<len(r)))
def det(A):
    n=len(A);S=Z
    for J in permutations(range(n)):
        T=O
        for i in range(n):T=red(T*A[i][J[i]])
        S+=(-1)**sum(J[i]>J[j] for i in range(n) for j in range(i+1,n))*T
    return red(S)

def remove(P,guards):
    out=[]
    for H in guards:
        if not H or not any(H.degrees()):
            out.append(0);continue
        K=con(H);Norm=red(H*K);m=0
        while True:
            T,R=divmod(red(P*K),Norm)
            if R:break
            P=red(T);m+=1
        out.append(m)
    return P,out

@lru_cache(None)
def profile(front):
    P,V,J=map(left,front_projection(front))
    A,B,m=map(lambda w:cv(F2,w),ends(front,1))
    ha,hb=(A-1)/2,(B-1-m)/2
    A,B,ha,hb=map(cast,(A,B,ha,hb));a,b,q=g*A,g*B,g*s
    La,Lb=ev(L4,a),ev(L4,b);Ga,Gb=ev(L3,a),ev(L3,b)
    D=red(g*(B-A)*La*Lb)
    Ap=[red(ha*Lb*b-hb*La*a), red(hb*La-ha*Lb)]
    Bp=[red(Ga*Lb*b-Gb*La*a), red(Gb*La-Ga*Lb)]
    h0=mul(list(map(C.constant,L4)),Ap);h1=mul(list(map(C.constant,L4)),Bp)
    h1=[red(D*(L3[i] if i<len(L3) else 0)-z) for i,z in enumerate(h1)]
    h=[red(V*e+P*w) for e,w in zip(h0,h1)]
    assert len(h)==6
    H4=red(sum(cast(cv(F2,w))*s**j for j,w in enumerate(pol(h4(front),lambda x:x))))
    assert not red(ev(h,a)-D*V*ha)
    assert not red(ev(h,b)-D*V*hb)
    assert not red(ev(h,q)-D*V*H4)
    return h,P,V,D,(a,b,q,La,Lb,A,B)

@lru_cache(None)
def raw(front,slot):
    h,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(front)
    x=1-g;c=x-g-g*v;d=x-g+g*v
    z={2:a,3:b,4:q}[slot]
    k=2-v*v
    Hx,Hc,Hd=map(lambda y:ev(h,y),(x,c,d))
    fu=red((1-v)*Hc-(1+v)*Hd+2*v*k*Hx)
    S,R=divmod(fu,v*(v*v-1));assert not R
    ff=centered(red(S));assert len(ff)==2
    A,B=ff
    G=red((x-z)*(Hc+Hd)/2-k*(x-g-z)*Hx)
    G=centered(G);assert len(G)==3
    C0=red(sum(V0*(-A)**j*B**(2-j) for j,V0 in enumerate(G)))
    early=[a,b,q]
    early.pop(slot-2)
    E=nodal([*early,x,c,d]);X=W(h)
    M=[]
    for j in range(4):
        P0=[Z]*j+E;U=W(P0)
        M.append([red(cof(h,U,i)-cof(P0,X,i)) for i in range(1,5)])
    N=centered(det(M));assert len(N)==5
    C1=red(sum(V0*(-A)**j*B**(4-j) for j,V0 in enumerate(N)))
    guards=[g,La,Lb,V,s-A0,s-B0,x-z,x-a,x-b,x-q]
    # x-a / x-b are guarded even when ordinarily silent: all nine
    # reverse sites distinct, not just the ordinary sites.
    W0,F0=remove(C0,guards);W1,F1=remove(C1,guards)
    assert F0==[8,3,3,0,0,0,0,0,0,0] and F1==[17,8,8,0,0,0,0,0,0,0]
    assert (W0.degrees()[1:3],W1.degrees()[1:3])==(((9,29),(26,79)) if slot<4 else ((10,29),(24,79)))
    print('regular star exact',front,slot,C0.degrees(),C1.degrees(),'stripped',W0.degrees(),W1.degrees(),
          'guard powers',F0,F1,flush=True)
    return W0,W1,A,B,guards

def evs(P,p,tr,g0):
    tab={}
    for (i,j,k,l),v0 in P.to_dict().items():
        assert i==0
        u=int(v0.p)*pow(int(v0.q),-1,p)%p
        tab[j]=(tab.get(j,0)+u*pow(g0,k,p)*pow(tr,l,p))%p
    return nmod_poly([tab.get(j,0) for j in range(max(tab,default=-1)+1)],p)

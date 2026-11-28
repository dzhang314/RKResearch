"""Exact split bounded-CRT resultants down to two variables over Q(t)."""
from regular_star_projection import C
from flint import nmod_mpoly_ctx
from math import gcd,lcm
from time import perf_counter
from sympy import nextprime,isprime

def int_input(F):
    D=1;M={}
    for (u,s,g,t),q0 in F.to_dict().items():
        assert t<=1
        q=q0/(2**t)
        a,b=int(q.p),int(q.q)
        M[(g,s,u),t]=(a,b);D=lcm(D,b)
    M={k:a*(D//b) for k,(a,b) in M.items()}
    h=gcd(*M.values())
    A={};B={}
    for (I,t),c in M.items():(B if t else A)[I]=c//h
    M=sum(map(abs,A.values()))+2*sum(map(abs,B.values()))
    return A,B,M

def image(F,N,p,z,cap,d):
    K=nmod_mpoly_ctx.get(['g','s','u'],p)
    ans=[];a,b=cap
    for sg in (z,p-z):
        Z=[K.from_dict({i:(U.get(i,0)+sg*V.get(i,0))%p for i in U.keys()|V.keys()})
            for U,V in (F,N)]
        if tuple(q.degrees()[2] for q in Z)!=d: return None
        R=Z[0].resultant(Z[1],2)
        A=[0]*((a+1)*(b+1))
        for (i,j,k),v in R.to_dict().items():
            assert not k and i<=a and j<=b
            A[i*(b+1)+j]=int(v)
        ans.append(A)
    q=pow(2,-1,p);r=pow(2*z,-1,p)
    return [[(x+y)*q%p for x,y in zip(*ans)],[(x-y)*r%p for x,y in zip(*ans)]]

def small_resultant(F,N):
    u0,s0,g0=F.degrees()[:3];u1,s1,g1=N.degrees()[:3]
    a,b=g0*u1+g1*u0,s0*u1+s1*u0
    A,B=int_input(F),int_input(N)
    bound=A[2]**u1*B[2]**u0
    coef=[[0]*((a+1)*(b+1)) for _ in range(2)]
    p=2**60;M=1;n=0;ts=perf_counter()
    while M<=2*bound:
        p=int(nextprime(p))
        if p%8!=7:continue
        R=image(A[:2],B[:2],p,pow(2,(p+1)//4,p),(a,b),(u0,u1))
        if R is None:continue
        inv=pow(M,-1,p)
        coef=[[v+M*((x-v)*inv%p) for v,x in zip(Ai,Bi)] for Ai,Bi in zip(coef,R)]
        M*=p;n+=1
        if n%8==0:print('small exact shape CRT',u0,u1,n,round(perf_counter()-ts,2),flush=True)
    coef=[[v if 2*v<M else v-M for v in Q] for Q in coef]
    assert all(abs(v)<=bound for Q in coef for v in Q)
    p0=1129;R=image(A[:2],B[:2],p0,406,(a,b),(u0,u1))
    assert all((v-w)%p0==0 for Q,S in zip(R,coef) for v,w in zip(Q,S))
    print('small CRT exact',u0,u1, (a,b),n,bound.bit_length(),round(perf_counter()-ts,2),flush=True)
    out={}
    for t,X in enumerate(coef):
        for n,v in enumerate(X):
            if v:
                i,j=divmod(n,b+1)
                out[(0,j,i,t)]=v*2**t
    return C.from_dict(out)

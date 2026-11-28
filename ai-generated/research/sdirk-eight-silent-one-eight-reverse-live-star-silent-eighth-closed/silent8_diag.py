"""Three exact factorwise integer resultants for the ordinary-silent eighth."""
from silent8_star_fifth import determinant_projection
from flint import fmpz_mpoly_ctx,fmpz_poly,nmod_mpoly_ctx
from functools import lru_cache
from time import perf_counter
from sympy import nextprime,isprime
from math import gcd,lcm

R=fmpz_mpoly_ctx.get(['g','s'])
def primitive(P):
    D={};d=1
    p=min(k for i,j,k,l in P.to_dict())
    for (i,j,k,l),w in P.to_dict().items():
        assert i==l==0
        a,b=int(w.p),int(w.q)
        D[k-p,j]=a,b
        d=lcm(d,b)
    D={K:a*(d//b) for K,(a,b) in D.items()}
    c=gcd(*D.values())
    return R.from_dict({k:w//c for k,w in D.items()}),p

@lru_cache(None)
def get_inputs():
    D,J,F,N,H,delta,dat=determinant_projection()
    D,vd=primitive(D);J,vj=primitive(J)
    assert vd==vj==0 and D.degrees()==(90,32)
    assert J.degrees()==(87,31)
    c,F=J.factor()
    assert F and sorted((A.degrees(),e) for A,e in F)==[((9,3),2),((23,11),1),((46,14),1)]
    G=J.context().constant(c)
    for A,e in F:G*=A**e
    assert G==J
    J3=next(A for A,e in F if A.degrees()[1]==3)
    W,v0=primitive(delta)
    assert W==J3 and v0==2
    return D,{A.degrees()[1]:A for A,e in F if A.degrees()[1]!=3}

def modular_resultant(P,Q,p):
    U,V=({key:int(z) for key,z in f.to_dict().items()} for f in (P,Q))
    g0,s0=P.degrees();g1,s1=Q.degrees();cap=g0*s1+g1*s0
    K=nmod_mpoly_ctx.get(['g','s'],p)
    A=K.from_dict({I:z%p for I,z in U.items()});B=K.from_dict({I:z%p for I,z in V.items()})
    if A.degrees()[1]!=s0 or B.degrees()[1]!=s1:return None
    W=[0]*(cap+1)
    for (j,i),c in A.resultant(B,1).to_dict().items():
        assert not i and j<=cap
        W[j]=int(c)
    return W

def exact_resultant(P,Q):
    U,V=[{key:int(z) for key,z in f.to_dict().items()} for f in (P,Q)]
    g0,s0=P.degrees();g1,s1=Q.degrees()
    cap=g0*s1+g1*s0
    bound=sum(map(abs,U.values()))**s1*sum(map(abs,V.values()))**s0
    coeff=[0]*(cap+1);modulus=1;p=2**60;count=0;now=perf_counter()
    assert (cap,bound.bit_length())=={11:(1726,4909),14:(2732,7550)}[s1]
    print('CRT start',s1,'cap',cap,'bound bits',bound.bit_length(),flush=True)
    while modulus<=2*bound:
        p=int(nextprime(p+1000))
        K=nmod_mpoly_ctx.get(['g','s'],p)
        A=K.from_dict({I:z%p for I,z in U.items()})
        B=K.from_dict({I:z%p for I,z in V.items()})
        if A.degrees()[1]!=s0 or B.degrees()[1]!=s1:continue
        W=[0]*(cap+1)
        for (j,i),c in A.resultant(B,1).to_dict().items():
            assert not i and j<=cap
            W[j]=int(c)
        inv=pow(modulus,-1,p)
        coeff=[z+modulus*((w-z)*inv%p) for z,w in zip(coeff,W)]
        modulus*=p; count+=1
        if count%12==0:print('CRT progress',s1,count,round(perf_counter()-now,1),flush=True)
    coeff=[v if 2*v<modulus else v-modulus for v in coeff]
    assert all(abs(v)<=bound for v in coeff)
    assert fmpz_poly(coeff).degree()==cap
    h=next(i for i,c in enumerate(coeff) if c)
    assert h=={11:177,14:320}[s1]
    X=fmpz_poly(coeff[h:]);X=X//X.content()
    # Guarded arithmetic independent clean additional prime.
    p0=1129
    E=modular_resultant(P,Q,p0)
    assert all((a-b)%p0==0 for a,b in zip(E,coeff))
    print('CRT exact end',s1,'cut gamma',h,'remaining',X.degree(),'primes',count,round(perf_counter()-now,2),flush=True)
    F=[];V0=fmpz_poly([1])
    for Y,e in X.factor_squarefree()[1]:
        for M,one in Y.factor()[1]:
            assert one==1
            F.append((M,e)); V0*=M**e
    assert V0==X or V0==-X
    print('exact factorwise gamma',s1,[(M.degree(),e) for M,e in F],flush=True)
    return X,F

"""Exact characteristic-zero diagonal restriction for the six-peg star interior."""
from regular_star_nonliteral import get_nonliteral
from regular_star_projection import con
from flint import fmpz_mpoly_ctx,nmod_mpoly_ctx,fmpz_poly,fmpq_poly
from sympy import nextprime
from math import lcm,gcd
from time import perf_counter

Z=fmpz_mpoly_ctx.get(['g','s'])
def primitive(P):
    vals={};L=1
    parity={I[-1] for I in P.to_dict()}
    assert len(parity)==1
    for (i,j,k,l),a in P.to_dict().items():
        assert i==0 and l in (0,1)
        v,w=int(a.p),int(a.q)
        L=lcm(L,w);vals[k,j]=(v,w)
    vals={e:v*(L//w) for e,(v,w) in vals.items()}
    D=gcd(*vals.values())
    return Z.from_dict({e:w//D for e,w in vals.items()})

def to_g(P):
    d={}
    for (i,j),a in P.to_dict().items():
        assert j==0
        d[i]=a
    return fmpz_poly([d.get(i,0) for i in range(max(d,default=-1)+1)])

def get_F():
    P,A,B=get_nonliteral(True)
    assert all(-P0==con(P0) for P0 in P)
    return list(map(primitive,P)),A,B

def exact_resultant_crt(P,Q):
    # For a Sylvester row the sum of polynomial coefficient 1-norms
    # equals the full coefficient 1-norm of its input. The determinant
    # 1-norm is at most the product of the row norms: summing over all
    # independent column choices bounds summing over permutations.
    U,V=({key:int(z) for key,z in f.to_dict().items()} for f in (P,Q))
    g0,s0=P.degrees();g1,s1=Q.degrees()
    cap=g0*s1+g1*s0
    bound=sum(map(abs,U.values()))**s1*sum(map(abs,V.values()))**s0
    coeff=[0]*(cap+1)
    modulus=1
    p=2**60
    count=0
    while modulus<=2*bound:
        p=int(nextprime(p+1000))
        K=nmod_mpoly_ctx.get(['g','s'],p)
        a=K.from_dict({I:v%p for I,v in U.items()})
        b=K.from_dict({I:v%p for I,v in V.items()})
        if (a.degrees()[1],b.degrees()[1])!=(s0,s1):
            continue
        out=[0]*(cap+1)
        for (i,j),v in a.resultant(b,1).to_dict().items():
            assert j==0 and i<=cap
            out[i]=int(v)
        inv=pow(modulus,-1,p)
        coeff=[x+modulus*((r-x)*inv%p) for x,r in zip(coeff,out)]
        modulus*=p
        count+=1
    coeff=[x if 2*x<modulus else x-modulus for x in coeff]
    assert all(abs(x)<=bound for x in coeff)
    print('exact bounded integer CRT',s0,s1,count,bound.bit_length(),flush=True)
    return fmpz_poly(coeff)

def factor_diagonal(independent_third=False,direct_integer=False):
    a0=perf_counter()
    F,A,B=get_F()
    N=None
    for j in ((1,2,3) if independent_third else (1,2)):
        print('exact resultant begin',j,F[0].degrees(),F[j].degrees(),flush=True)
        H=(to_g(F[0].resultant(F[j],1)) if direct_integer else exact_resultant_crt(F[0],F[j]))
        assert H.degree()=={1:1871,2:1810,3:1816}[j]
        h=min(i for i,c in enumerate(H) if c)
        assert h=={1:310,2:302,3:316}[j]
        H=H.right_shift(h);H=H//H.content()
        N=H if N is None else N.gcd(H)
        print('exact resultant done',j,h+H.degree(),h,'gcd',N.degree(),perf_counter()-a0,flush=True)
    assert N.degree()==1213
    print('exact factor begin',N.degree(),flush=True)
    prod=fmpz_poly([1]);out=[]
    for X,e in N.factor_squarefree()[1]:
        print('squarefree',e,X.degree(),perf_counter()-a0,flush=True)
        for P,k in X.factor()[1]:
            assert k==1
            prod*=P**e
            M=fmpq_poly(P)
            out.append((M*(1/M[M.degree()]),e))
            print('factor',e,P.degree(),perf_counter()-a0,flush=True)
    assert prod==N or prod==-N
    print("exact common gamma factorization", [(M.degree(),e) for M,e in out],flush=True)
    return out

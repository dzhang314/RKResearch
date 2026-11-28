"""Bounded exact rational resultants and a full verified guard product."""
import os
from multiprocessing import get_context,get_all_start_methods
from time import perf_counter
from functools import lru_cache
from flint import fmpz_poly,fmpz_mpoly_ctx
from sympy import nextprime
from rear5_model import model5
from rear67_exact import full_native
from silent8_diag import primitive,modular_resultant
from check_star_arithmetic67 import s_coeffs
from geometric_outer import img,compiler

AB=None

def image(A,B,p):
    # The original independent exact interpolation / resultant fallback
    # has all the same degree guards and includes no geometric ABI assumption.
    Z=img(A,B,p) if compiler() else None
    return full_native(A,B,p) if Z is None else Z

def worker(p):
    return image(*AB,p)

def result(A,B,tag,use_fork=False):
    global AB
    AB=A,B
    ga,sa=A.degrees();gb,sb=B.degrees()
    cap=ga*sb+gb*sa
    bound=sum(abs(int(m)) for m in A.to_dict().values())**sb*sum(abs(int(m)) for m in B.to_dict().values())**sa
    PP=[];m=1;p=2**60
    while m<=2*bound:
        p=int(nextprime(p+1000));PP.append(p);m*=p
    t0=perf_counter();Z=[0]*(cap+1);m=1
    # Full initial and independent verification images, not sampled gamma entries.
    first=worker(PP[0])
    assert first==full_native(A,B,PP[0])
    if not use_fork:
        assert first==modular_resultant(A,B,PP[0])
    def collect(stream):
        nonlocal m,Z
        for i,x in enumerate(stream):
            p=PP[i]
            assert x is not None and len(x)==cap+1
            b=pow(m,-1,p)
            for j,w in enumerate(x):Z[j]+=m*((w-Z[j])*b%p)
            m*=p
            if use_fork and (i+1)%32==0:
                print('outer exact CRT',i+1,round(perf_counter()-t0,2),flush=True)
    k=max(1,min(3,int(os.environ.get('RK_CRT_WORKERS','1'))))
    if use_fork and k>1 and 'fork' in get_all_start_methods():
        with get_context('fork').Pool(k) as work:
            collect(work.imap(worker,PP))
    else:
        collect(map(worker,PP))
    assert m>2*bound
    for j,z in enumerate(Z):
        if 2*z>=m:Z[j]=z-m
    assert any(Z) and all(abs(z)<=bound for z in Z)
    v=next(i for i,z in enumerate(Z) if z)
    X=fmpz_poly(Z)
    p1=65537 if use_fork else 1129
    if use_fork:
        E=full_native(A,B,p1);assert E==worker(p1)
    else:
        E=modular_resultant(A,B,p1)
    assert E and all((z-e)%p1==0 for z,e in zip(Z,E))
    shape=(cap,bound.bit_length(),X.degree(),v,len(PP))
    print('exact rational resultant',tag,shape,flush=True)
    Y=X.right_shift(v)
    return Y//Y.content(),shape

# Exact source factor label -> complete AB multiplicity, exact
# fourth size, forbidden support kind and size, local component count.
PLAN={
    ('lead',1,6):(2,46,None,0,2),
    ('lead',2,3):(9,46,'nodal_lead',1,3),
    ('lead',6,4):(342,42,'nodal_lead',12,1),
    ('terminal_h',3,5):(3,48,'terminal_h',3,3),
    ('terminal_h',3,46):(3,48,'terminal_h',3,5),
    ('terminal_h',6,30):(36,48,'nodal_lead',6,8),
    ('terminal_h',12,21):(168,48,'nodal_lead',12,2),
    ('terminal_h',12,9):(72,48,'nodal_lead',12,2),
    ('terminal_h',18,4):(108,48,'nodal_lead',18,3),
    ('nodal_lead',4,24):(2,48,'nodal_lead',2,3),
    ('nodal_lead',6,12):(37,48,'nodal_lead',6,7),
}

@lru_cache(None)
def small_guard_factors():
    A,B,T=model5()
    a,b=(fmpz_poly(list(s_coeffs(P)[-1])) for P in (A,B))
    D=a.gcd(b);F=D.factor()[1]
    assert sorted((M.degree(),e) for M,e in F)==[(1,48),(3,2),(4,6),(6,1)]
    assert next(M for M,e in F if M.degree()==1) in (fmpz_poly([0,1]),fmpz_poly([0,-1]))
    Z=[(('lead',e,M.degree()),M) for M,e in F]
    for name in ('terminal_h','nodal_lead'):
        G,v=primitive(T['guards'][name])
        Q,shape=result(A,G,name)
        assert shape=={
            'terminal_h':(924,2406,924,159,41),
            'nodal_lead':(1884,5172,1884,222,87),
        }[name]
        P=fmpz_poly([1])
        for X,e in Q.factor_squarefree()[1]:
            F=X.factor()[1]
            for M,k in F:
                assert k==1
                P*=M**e
                Z.append(((name,e,M.degree()),M))
        assert P==Q or P==-Q
    C={}
    for k,M in Z:
        if k in PLAN:
            assert k not in C
            # Canonical sign avoids unneeded signs in the product.
            C[k]=M if M[M.degree()]>0 else -M
    assert C.keys()==PLAN.keys()
    return C

def cover(F):
    C=small_guard_factors()
    Q=F
    del F
    total=0
    for key,M in C.items():
        P=M**PLAN[key][0]
        total+=P.degree()
        Q,R=divmod(Q,P)
        assert not R
    assert total==7740 and Q.degree()==4923
    return Q,C

def check_padding_control():
    if compiler() is None:return
    K=fmpz_mpoly_ctx.get(['g','s']);g,s=K.gens()
    # At g=1 both leads drop; at g=4 only Q; at g=16 only P.
    A=(g-1)*(g-16)*s**2+(g+1)*s+7
    B=(g-1)*(g-4)*s**3+(g+2)*s*s+2*s+11
    assert img(A,B,65537)==modular_resultant(A,B,65537)
    print('geometric control: both leading drops and each one-sided drop',flush=True)

def diagonal():
    check_padding_control()
    A,B,D=model5()
    E,shape=result(A,B,'whole silent five',use_fork=True)
    assert shape==(14616,41273,14616,1953,688)
    return E

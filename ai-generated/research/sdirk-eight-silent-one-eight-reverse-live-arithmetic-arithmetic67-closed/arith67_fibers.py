"""Actual arithmetic literal third and two possible physical silent slots."""
from arith67_model import model
from arith67_outer import I,oriented
from arith_star_diagonal import int_input
from check_star_arithmetic67 import gfiber
from star4_actual_fifth import Bfield,gcdp,nmod_poly
from functools import lru_cache

@lru_cache(None)
def all_int():
    return tuple(int_input(x) for x in model()[:3])
@lru_cache(None)
def int_mod(p,t):
    z=2*t%p;assert z*z%p==2
    L=[]
    for A,B,_ in all_int():
        L.append(I.from_dict({j:(A.get(j,0)+z*B.get(j,0))%p for j in A.keys()|B.keys()}))
    assert [P.degrees() for P in L]==[(132,48),(156,54),(69,32)]
    return L

def all_mod(R,p,t,s0=None):
    A,B,J=int_mod(p,t)
    count=0;covered=nmod_poly([1],p)
    for P,e in R.factor()[1]:
        covered*=P**e
        K=Bfield(P,p,t)
        U=[gfiber(Q,K) for Q in (A,B,J)]
        if s0 is None:
            S=next((W for W,d in zip(U,(48,54,32)) if len(W)==d+1),None)
            assert S is not None
        else:
            S=[K(z.v) for z in s0]
            assert S and S[-1]==1
        for T in U:S=gcdp(S,T)
        assert len(S)==1
        count+=1
    assert covered==R
    return count

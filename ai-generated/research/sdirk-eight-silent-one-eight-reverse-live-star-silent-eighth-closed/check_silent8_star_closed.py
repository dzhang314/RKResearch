"""Exact closure of the regular star-front constant numerator, actual silent eight.

Pinned: sympy==1.14.0, python-flint==0.9.0.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
from flint import fmpq_poly
from sympy import isprime
import sys

ROOT=Path(__file__).resolve().parent.parent
DEPS=(
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-exceptional",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-regular-silent-eighth-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed",
    "sdirk-eight-silent-one-seven-distinct-anchors",
    "sdirk-eight-silent-one-seven-distinct-coprime",
    "sdirk-eight-silent-one-seven-six-anchored",
    "sdirk-eight-silent-one-seven-six-reverse",
    "sdirk-eight-silent-one-seven-six-shared",
    "sdirk-eight-silent-three-closure",
    "sdirk-eight-silent-two-equal",
    "sdirk-eight-silent-two-high",
    "sdirk-eight-silent-two-unequal",
)
for dep in DEPS:
    sys.path.append(str(ROOT/dep))

from silent8_diag import get_inputs,exact_resultant
from silent8_fibers import true_guards,all_mod,Field,sc,trim
from silent8_support import exact_support_division

# (degree, exponent): (exact nodal-leading support removed, expected reduced test, count).
# None denotes the nominal-degree unguarded local model; 0 retains the
# actual exact degree at this entire diagonal factor before monicization.
PLAN={
    11:{
      (3,1):(0,'no_s',1),
      (143,1):(None,'no_distinct_fifth',8),
      (693,1):(None,'actual_chronology',5),
      (30,4):(4,'no_s',8),
      (9,4):(4,'no_s',4),
      (12,5):(5,'no_s',12),
      (4,12):(12,'no_s',4),
      (21,14):(7,'no_s',2),
      (4,38):(10,'no_s',2),
    },
    14:{
      (24,1):(1,'no_s',5),
      (232,1):(None,'no_distinct_fifth',4),
      (402,2):(None,'actual_chronology',6),
      (9,4):(4,'no_s',4),
      (30,8):(4,'no_s',8),
      (12,10):(5,'no_s',12),
      (4,24):(12,'no_s',4),
      (21,28):(7,'no_s',2),
      (4,68):(10,'no_s',2),
    },
}

@lru_cache(None)
def basis():
    D,_=get_inputs()
    _,G,_=true_guards()
    V={}
    for (i,j),v in D.to_dict().items():
        V.setdefault(j,{})[i]=v
    P=tuple(fmpq_poly([V.get(j,{}).get(i,0)
      for i in range(max(V.get(j,{}),default=-1)+1)]) for j in range(max(V)+1))
    return P,G

def fourth(M,n):
    P,G=basis()
    K=Field(M)
    F=trim(list(map(K,P)));F0=trim(list(map(K,G)))
    assert F and F0
    if n:
        F=exact_support_division(F,F0,n,K)
    return sc(F,F[-1].inv())

def check_factors(L,factors):
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    plan=PLAN[L]
    assert sorted((M.degree(),e) for M,e in factors)==sorted(plan)
    totals=Counter()
    for M,e in factors:
        M=fmpq_poly(M); M*=1/M[M.degree()]
        n,kind,c=plan[M.degree(),e]
        S=None if n is None else fourth(M,n)
        ok,tracks,err=all_mod(M,e,L,p,t,S)
        assert ok and not err and Counter(tracks)=={kind:c}
        totals.update(tracks)
    return totals

def main():
    D,J=get_inputs()
    assert set(J)=={11,14}
    tally=Counter()
    for L in (11,14):
        _,F=exact_resultant(D,J[L])
        tally.update(check_factors(L,F))
    assert tally=={'no_s':70,'no_distinct_fifth':12,'actual_chronology':11}
    print("regular star-front constant numerator with actual silent eighth excluded",
          dict(tally),flush=True)

if __name__=='__main__':
    main()

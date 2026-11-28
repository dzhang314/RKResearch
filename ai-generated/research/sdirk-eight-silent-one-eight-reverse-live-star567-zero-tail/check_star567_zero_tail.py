"""Exact full diagonal/fourth/rear-gap towers for the zero star-tail chart."""
from pathlib import Path
from itertools import combinations
import sys
from sympy import isprime

ROOT = Path(__file__).resolve().parent.parent
DEPS = (
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-zero-tail",
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

from zero_tail_rank import (
    DU, Bfield, Tower, Nested, add, bcol, det, ex_constants, model,
    mul, nmod_poly, nodal, sc, trim,
)


class UP:
    def __init__(self,L):self.L=trim(L)
    def c(self,x):return x if isinstance(x,UP) else UP([x])
    def __add__(self,y):return UP(add(self.L,self.c(y).L))
    __radd__=__add__
    def __neg__(self):return UP(sc(self.L,-1))
    def __sub__(self,y):return self+-self.c(y)
    def __rsub__(self,y):return self.c(y)+-self
    def __mul__(self,y):return UP(mul(self.L,self.c(y).L))
    __rmul__=__mul__
    def __truediv__(self,y):return UP([x/y for x in self.L])
    def __bool__(self):return bool(self.L)

class UPO:
    def __init__(self,U):self.U=U
    def __call__(self,x):return x if isinstance(x,UP) else UP([self.U(x)])

def polys(p,t,verbose=True):
    raw=nmod_poly([-5,18],p)*nmod_poly(list(DU),p)
    assert raw.degree() == 5 and raw.leading_coefficient() == 18*1400 % p
    factors = raw.factor()[1]
    assert sorted((M.degree(),e) for M,e in factors) == [(1,1),(1,1),(1,1),(2,1)]
    counts=[]
    for M,e in factors:
        K=Bfield(M,p,t);g=K(nmod_poly([0,1],p));g.inv()
        L,S,(a,b,ha,hb,H4)=model(K,g)
        assert len(S) == 4
        U=Tower(sc(S,S[-1].inv()));s=U.gen();GL=list(map(U,L))
        gg=U(g); x=1-gg; m=1-2*gg; q=gg*s
        O=UPO(U); w=UP([U(0),U(1)])
        E=mul(nodal(list(map(O,[gg*U(a),gg*U(b),q,x]))),[O(m*m)+O(-gg*gg)*w,O(-2*m),O(1)])
        H=list(map(O,GL))
        J=[bcol([O(0)]*i+E,H,O) for i in range(3)]
        N=[det([[J[j][i] for i in I] for j in range(3)]).L for I in combinations(range(4),3)]
        if verbose: print('gamma',M.degree(),'s',len(S)-1,'degrees',[len(q)-1 for q in N],flush=True)
        # All these polynomials are cubics at most by construction:
        # each matrix entry is affine in the unordered rear parameter.
        # The first one is degree exactly three with invertible leading
        # coefficient at every retained k[gamma,s] component.
        assert [len(q)-1 for q in N] == [3,3,3,3]
        T = Nested(sc(N[0],N[0][-1].inv()))
        for F in N[1:]:
            T(F).inv()
        counts.append(M.degree())
    return sorted(counts)

def main():
    p, t = 1097, 345
    assert isprime(p) and (2*t*t-1) % p == 0
    ex_constants()
    assert polys(p,t) == [1,1,1,2]
    print("all regular zero-tail silent physical 5/6/7 cases excluded",flush=True)

if __name__ == "__main__":
    main()

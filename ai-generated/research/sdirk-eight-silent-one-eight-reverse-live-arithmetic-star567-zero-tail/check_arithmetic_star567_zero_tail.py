"""Arithmetic front / star rear: zero centered tail on the six-peg placement."""
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parent.parent
DEPS=(
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-zero-tail",
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

from zero_tail_rank import (
    QU,PU,ex_constants,add,sc,qr,ev,nodal,mul,
    Bfield,Tower,Nested,bcol,det,nmod_poly,trim,
)
from regular_star_projection import g,red,ev as exev,cast,Co,remove
from mixed_front_projection import L3,L4,L5
from seven_k0_anchors import ends,h4,pol,F2,cv
from star4_actual_fifth import lv
from itertools import combinations
from functools import lru_cache
from sympy import isprime

@lru_cache(None)
def exact_data():
    ex_constants()
    (a,b,m)=map(lambda w:cast(cv(F2,w)),ends(False,1))
    ha,hb=red((a-1)/2),red((b-1-m)/2)
    Q,P=exev(QU,g),exev(PU,g)
    H=[red(-8*P*(L3[j] if j<4 else 0)+(162*g-45)*Q*(L4[j] if j<5 else 0)+5*Q*L5[j]) for j in range(6)]
    L=red(hb*exev(H,g*a)-ha*exev(H,g*b))
    U,counts=remove(L,[g,Q])
    assert U.degrees()==(0,0,8,1) and counts==[0,0]
    print('exact arithmetic zero tail gamma',L.degrees(),U.degrees(),counts,flush=True)
    return U,H,(a,b,m,ha,hb)

class UP:
    def __init__(self,L):self.L=trim(L)
    def c(self,x):return x if isinstance(x,UP) else UP([x])
    def __add__(self,y):return UP(add(self.L,self.c(y).L))
    __radd__=__add__
    def __neg__(self):return UP(sc(self.L,-1))
    def __sub__(self,y):return self+-self.c(y)
    def __rsub__(self,x):return self.c(x)+-self
    def __mul__(self,y):return UP(mul(self.L,self.c(y).L))
    __rmul__=__mul__
    def __truediv__(self,y):return UP([x/y for x in self.L])
    def __bool__(self):return bool(self.L)
class Polynomials:
    def __init__(self,K):self.K=K
    def __call__(self,x):return x if isinstance(x,UP) else UP([self.K(x)])

def test(p,t,verbose=True):
    F,HH,base=exact_data()
    W=Bfield(nmod_poly([0,1],p),p,t)
    n=F.degrees()[2]
    raw=nmod_poly([int(lv(P,W,W(0),W(0),p,t).x[0]) for P in Co(F,2)],p)
    if raw.degree()!=n:raise ArithmeticError('gamma leading')
    all0=[]
    for M,e in raw.factor()[1]:
        K=Bfield(M,p,t);g=K(nmod_poly([0,1],p));g.inv()
        get=lambda P:lv(P,K,g,K(0),p,t)
        a,b,m,ha,hb=map(get,base)
        L=list(map(get,HH))
        L=sc(L,ha/ev(L,g*a));assert ev(L,g*b)==hb
        H4=[cv(K,w) for w in pol(h4(False),lambda x:x)]
        S,r=qr(add([v*g**i for i,v in enumerate(L)],sc(H4,-1)),nodal([a,b]))
        assert not r
        if len(S)!=4:raise ArithmeticError('fourth leading')
        U=Tower(sc(S,S[-1].inv()));s=U.gen()
        g,a,b=map(U,(g,a,b));x=1-g;m=1-2*g
        O=Polynomials(U);w=UP([U(0),U(1)])
        E=mul(nodal(list(map(O,[g*a,g*b,g*s,x]))),[O(m*m)-O(g*g)*w,O(-2*m),O(1)])
        H=list(map(O,map(U,L)))
        J=[bcol([O(0)]*i+E,H,O) for i in range(3)]
        N=[det([[J[j][i] for i in I] for j in range(3)]).L for I in combinations(range(4),3)]
        assert len(N[0])==4
        T=Nested(sc(N[0],N[0][-1].inv()))
        T(N[1]).inv()
        found=(0,1)
        all0.append((M.degree(),e,*found))
        if verbose: print('full reduced gamma',M.degree(),e,found,flush=True)
    return sorted(all0)

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    assert test(p,t)==[(1,1,0,1),(7,1,0,1)]
    print("arithmetic front / star rear, silent 5/6/7, zero centered tail excluded",
          flush=True)

if __name__=="__main__":
    main()

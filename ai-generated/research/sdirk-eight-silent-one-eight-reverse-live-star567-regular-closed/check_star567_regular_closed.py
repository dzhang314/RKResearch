"""Complete regular star–star interior placements with nonzero centered B.

Reproduction: sympy==1.14.0, python-flint==0.9.0.
"""
from argparse import ArgumentParser
from pathlib import Path
import sys
from sympy import isprime

ROOT = Path(__file__).resolve().parent.parent
DEPS = (
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
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

from star567_exact_diagonal import factor_diagonal
from star567_fibers import Field, all_mod, bounds, sc, trim
from star567_support import exact_support_division

# (degree, exponent) : (lawful exact guard, removed s-degree, full reduced count).
PLAN = {
    (257,1):(None,0,2),
    (35,2):("regular_scale",2,4),
    (2,2):("regular_scale",2,2),
    (9,2):("regular_scale",2,4),
    (27,3):("terminal_h",3,4),
    (4,6):("regular_scale",4,2),
    (21,25):("rear_a",5,2),
    (1,27):("rear_a",9,1),
    (4,27):("w2",0,0),
    (3,33):("rear_a",3,1),
}

def exact_guarded_fourth(M, guard, removed):
    P, _, J = bounds()
    K = Field(M)
    F = trim(list(map(K,P[0])))
    G = trim(list(map(K,dict(J)[guard])))
    assert G and F
    F = exact_support_division(F,G,removed,K)
    return sc(F,F[-1].inv())

def check_fibers(factors):
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    assert sorted((M.degree(),e) for M,e in factors)==sorted(PLAN)
    n=0
    for M,e in factors:
        d=M.degree()
        guard,removed,c=PLAN[d,e]
        if guard=="w2":
            _, _, J = bounds()
            K=Field(M)
            assert not trim(list(map(K,dict(J)[guard])))
            assert removed==c==0
            print("exact entire gamma component forces k=0",d,e,flush=True)
            continue
        F=None if guard is None else exact_guarded_fourth(M,guard,removed)
        ok,count,bad=all_mod(M,p,t,F)
        assert ok and not bad and count==c
        n+=count
        print("complete diagonal factor",d,e,guard,removed,c,flush=True)
    assert n==22
    print("all regular nonzero-tail silent physical 5/6/7 cases excluded",flush=True)

def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--independent-third",action="store_true")
    parser.add_argument("--direct-integer",action="store_true",help="skip CRT and compute integer resultants directly")
    args=parser.parse_args()
    check_fibers(factor_diagonal(args.independent_third,args.direct_integer))

if __name__=="__main__":
    main()

"""Full exact star-front/star-rear regular chart with ordinarily silent physical fourth."""
from pathlib import Path
from sympy import isprime
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-eight-reverse-live-constant",
            "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from star4_exact_diagonal import factor_diagonal
from star4_guarded_fibers import PLAN,one_factor

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    factors=factor_diagonal()
    assert sorted((M.degree(),e) for M,e in factors)==sorted(PLAN)
    for M,e in factors:
        one_factor(M,e,p,t)
        print('complete exact gamma factor excluded',M.degree(),e,flush=True)
    print('all twelve regular star-star literal silent-fourth factors excluded',flush=True)

if __name__=='__main__':
    main()

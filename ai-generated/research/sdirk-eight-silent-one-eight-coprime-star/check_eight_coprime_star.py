"""All eight-active reverse-star fibers, with and without a Gauss tail peg."""
from pathlib import Path
from sympy import isprime
import sys

root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from star_fibers import verify
from star_gauss import verify_gauss

def main():
    for front,p,t,ordinary,gauss in ((True,1103,161,(6,6,6),(7,11,11)),
                                    (False,1097,345,(1,1,1),(12,21,21))):
        assert isprime(p) and (2*t*t-1)%p==0
        op=verify(front,p,t,True)
        assert op==ordinary
        print('no Gauss tail:',front,p,t,op,flush=True)
        assert isprime(1097) and (2*345*345-1)%1097==0
        gh=verify_gauss(front,1097,345,True)
        assert gh==gauss
        print('Gauss tail:',front,1097,345,gh,flush=True)
    print('all four coprime rear-star modes excluded',flush=True)

if __name__=='__main__':
    main()

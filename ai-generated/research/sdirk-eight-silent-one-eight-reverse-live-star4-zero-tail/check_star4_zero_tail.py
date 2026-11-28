"""Full exact degeneracy branch of the centered star relation."""
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
from zero_tail_rank import ex_constants,test

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    ex_constants()
    assert test(p,t)==3
    print('all identically zero centered star tails excluded in this chart',flush=True)

if __name__=='__main__':
    main()

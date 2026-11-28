"""Full exact finite-diagonal witness for ordinarily silent physical eighth."""
from pathlib import Path
from sympy import isprime
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-eight-reverse-live-constant",
            "sdirk-eight-silent-one-eight-reverse-live-exceptional",
            "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from regular_silent_eighth import test_at

def main():
    p,t,g=1129,203,2
    assert isprime(p) and (2*t*t-1)%p==0
    assert test_at(True,p,t,g)==[5,5]
    assert test_at(False,p,t,g)==[4,4]
    print('both regular ordinarily silent-eighth phases have finite characteristic-zero diagonals',flush=True)

if __name__=='__main__':
    main()

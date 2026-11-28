"""All intended degree-21 exceptional constant-T mixed-quintic orientations."""
from pathlib import Path
from sympy import isprime
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-eight-reverse-live-constant",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from exception_final import check_modes
from head21 import check_head

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    check_head()
    for f,expected in ((True,[12,4,2]),(False,[18,6,3])):
        assert check_modes(f,p,t,True)==expected
    print('all degree-21 exceptional mixed-quintic orientations excluded',flush=True)

if __name__=='__main__':
    main()

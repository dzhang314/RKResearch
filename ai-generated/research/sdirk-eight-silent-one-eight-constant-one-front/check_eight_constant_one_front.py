"""Replay all four literal front choices and both active rear phases."""
from pathlib import Path
from sympy import isprime
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-distinct-one-front-zero",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from one_front_constant_fibers import check

def main():
    p,t=1097,345
    assert isprime(p) and (2*t*t-1)%p==0
    for front,slot,counts in ((True,0,(12,5,5,5)),(True,1,(16,9,9,9)),
                             (False,0,(10,7,7,7)),(False,1,(6,3,3,3))):
        for rear in (True,False):
            r=check(front,slot,rear,p,t)
            assert r==counts
            print('verified one-front constant phase',front,slot,rear,p,t,r,flush=True)
    print('all eight one-front constant-numerator modes excluded',flush=True)

if __name__=='__main__':
    main()

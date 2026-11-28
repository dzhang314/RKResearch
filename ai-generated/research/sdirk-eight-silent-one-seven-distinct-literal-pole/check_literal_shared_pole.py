"""Exact one-front/no-extra check; run from the sibling repository proof tree."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime"):
    sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from literal_shared_pole_front import silent5
from literal_shared_pole_late import verify_late

def main():
    p,t=1103,161
    assert isprime(p) and (2*t*t-1)%p==0
    n=m=0
    for f,i in product((True,False),(0,1)):
        assert silent5(f,i)==0;n+=1
        for j in (True,False,None):
            assert verify_late(f,i,j,p,t);m+=1
    assert (n,m)==(4,12)
    print('one-front shared-pole checks:',n,m)

if __name__=='__main__':main()

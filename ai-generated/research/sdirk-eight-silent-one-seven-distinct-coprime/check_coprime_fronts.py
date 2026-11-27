"""Exact isolated checks for the final both-front seven-clock subcase."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared"):
    sys.path.insert(0,str(root/dep))
from sympy import isprime
from no_extra import mode
from five_peg_checks import verify
from silent_extra import verify_silent

def main():
    p,t=1103,161
    assert isprime(p) and (2*t*t-1)%p==0
    A=B=C=0
    for f in (True,False):
        for j in (None,True,False):
            assert mode(f,j,p,t);A+=1
        for j in (True,False):
            assert verify(f,j,p,t);B+=1
        assert verify_silent(f,p,t);C+=1
    assert (A,B,C)==(6,4,2)
    print('both-front coprime seven-clock orientations excluded:',A,B,C)
if __name__=='__main__':main()

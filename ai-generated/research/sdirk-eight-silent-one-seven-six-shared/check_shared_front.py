"""Exact verification of all the shared-root and active Gauss-front subcharts."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse"):
    sys.path.insert(0,str(root/dep))

from itertools import product
from sympy import isprime
from shared_literal import check as shared, zgauss
from gauss_separate import verify as separate

def main():
    p,t=1009,285
    assert isprime(p) and 2*t*t%p==1
    S=G=0
    for f,slot in product((True,False),(0,1)):
        for j,h in product((True,False),(0,8,9,10)):
            assert shared(f,slot,j,h,False,p,t);S+=1
        for h in (0,9,10):
            assert shared(f,slot,True,h,True,p,t);S+=1
        for j in (True,False):
            assert zgauss(f,slot,j,p,t);S+=1
        for j,h in product((True,False),(0,8,9)):
            assert separate(f,slot,j,h,False,p,t);G+=1
        for h in (0,9):
            assert separate(f,slot,True,h,True,p,t);G+=1
    assert (S,G)==(52,32)
    print('shared and active Gauss-front orientations excluded:',S,G)
if __name__=='__main__':main()

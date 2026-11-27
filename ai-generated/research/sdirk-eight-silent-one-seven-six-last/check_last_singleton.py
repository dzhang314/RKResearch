"""Exact characteristic-zero replay of the last independent six-clock chart."""
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

from itertools import product
from sympy import isprime
from flint import nmod_poly
from nong_tail import mod_u,Lco
from nong_check import verify_other

def guard(p,t):
    assert isprime(p) and (2*t*t-1)%p==0
    rr=nmod_poly(list(Lco),p).roots()
    assert len(rr)==4 and all(m==1 for _,m in rr)

def main():
    n=0
    for f,slot in product((True,False),(0,1)):
        for branch in (4,5,0):
            p,t=(1783,79) if branch==5 and not f and slot==0 else ((1559,529) if not f and slot==0 else (1129,203))
            guard(p,t)
            assert not mod_u(f,slot,branch,p,t)
            assert not verify_other(f,slot,branch,p,t)
            n+=1
    assert n==12
    print('all last singleton-front orientations excluded:',n)
if __name__=='__main__':main()

"""Exact offline replay of the last zero-factor and both-front-silent charts."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high",
            "sdirk-eight-silent-one-seven-six-anchored"):
    sys.path.insert(0,str(root/dep))

from itertools import product
from sympy import isprime
from one_front_zero import B0,gcdp,verify as zero
from no_front_nonzero import verify as nonzero
from arithmetic_nonzero import precheck as arithmetic

def main():
    p,t=1009,285
    assert isprime(p) and 2*t*t%p==1
    H=list(map(B0,[-2,1,4,-1]))
    C=list(map(B0,[2,3,-12,4]))
    assert len(gcdp(H,C))==1
    zct=nct=act=0
    for front,z in product((True,False),(0,1)):
        for rear,s in product((None,True,False),(1,-1)):
            for hit in ('','0','9')+(('8',) if rear is not None else ()):
                assert zero(front,z,rear,s,hit,p,t)
                zct+=1
        for rear,hit in product((True,False),(0,8,9,10)):
            if rear or hit:
                assert nonzero(front,z,rear,hit,p,t)
                nct+=1
        assert arithmetic(front,z,p,t)
        act+=1
    assert (zct,nct,act)==(88,28,4)
    print('all reverse-support orientations excluded:',zct,nct,act)
if __name__=='__main__':main()

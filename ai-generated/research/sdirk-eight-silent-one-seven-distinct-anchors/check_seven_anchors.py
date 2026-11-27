"""Exact scoped seven-distinct closures with both literal fronts active."""
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
from flint import nmod_poly
from seven_k0_anchors import hole_terminal,use,Lco
from constant_q_nonzero import gamma_factors,test

def guard(p,t):
    assert isprime(p) and (2*t*t-1)%p==0

def main():
    p,t=1103,161
    guard(p,t)
    guard(1129,203)
    assert len(nmod_poly(list(Lco),1129).roots())==4
    H=Q=T=0
    for rear,ori in product((True,False),(1,-1)):
        hole_terminal(rear,ori,1129,203);H+=1
    for front,rear,ori in product((True,False),(None,True,False),(1,-1)):
        assert use(front,rear,ori,p,t);Q+=1
    for front in (True,False):
        fs=gamma_factors(front)
        assert list(map(lambda X:X.degree(),fs))==[4]
        for rear,extra in [(j,h) for j,h in product((True,False),(True,False))]+[(None,True)]:
            assert test(front,fs[0],rear,extra,p,t);T+=1
    assert (H,Q,T)==(4,12,10)
    print('seven-distinct scoped orientations excluded:',H,Q,T)
if __name__=='__main__':main()

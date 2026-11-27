"""Reproducible characteristic-zero proof of the dependent six-clock census."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high",
            "sdirk-eight-silent-one-seven-small","sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse","sdirk-eight-silent-one-seven-six-shared"):
    sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from dependent_tail import check,h4
from terminal_both_fourth_ordinary import verify as ordinary
from terminal_fourth_special import verify as special
from triple_silent8 import both_low

def guard(p,t):
    assert isprime(p) and (2*t*t-1)%p==0

def main():
    p,t=1103,161
    guard(p,t)
    guard(1009,285)
    T=U=V=W=0
    for f,slot,hit in product((True,False),(0,1),(9,10)):
        assert check(f,slot,False,hit,True,1,p,t);T+=1
        for j,o in product((True,False),(1,-1)):
            assert check(f,slot,j,hit,False,o,p,t);T+=1
        for gap in ((2,1+2*t,1-2*t) if hit==9 else (2,)):
            assert both_low(f,hit,slot,p,t,gap);U+=1
    for f,rear,sg in product((True,False),(True,False),(1,-1)):
        fac=h4(f).factor_list()[1]
        assert [(q.degree(),m) for q,m in fac]==[(3,1)]
        p0,t0=(1009,285) if f and not rear and sg==-1 else (p,t)
        assert ordinary(f,rear,sg,fac[0][0].monic(),p0,t0);V+=1
        for which in (None,0,1):
            assert special(f,which,rear,sg,p,t);W+=1
    assert (T,U,V,W)==(40,16,8,24)
    print('dependent six-clock orientations excluded:',T,U,V,W)
if __name__=='__main__':main()

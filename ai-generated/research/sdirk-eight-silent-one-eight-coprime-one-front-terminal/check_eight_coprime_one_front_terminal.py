"""A live terminal Gauss clock, one active literal front, all literal phases."""
from pathlib import Path
from sympy import isprime
import sys

root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-eight-shared-gauss-one-front",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from coprime_terminal_fibers import test,root_consts

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    assert root_consts(p)==[100,214,916,1030]
    for f,a,n in ((True,0,15),(True,1,14),(False,0,12),(False,1,8)):
        for h in (True,False):
            z=test(f,a,h,p,t,True)
            assert z==(n,n,n)
            print('verified coprime terminal phase',f,a,h,z,flush=True)
    print('all eight one-front coprime Gaussian terminal modes excluded',flush=True)

if __name__=='__main__':
    main()

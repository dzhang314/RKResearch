"""All eight finite-free coprime projection matrices, without an RK tableau reduction."""
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
from coprime_one_front_matrix import test_matrix

def main():
    p,t=1097,345
    assert isprime(p) and (2*t*t-1)%p==0
    for f,a,h,ga,n,d in (
        (True,0,True,2,42,906),(True,0,False,2,105,667),
        (True,1,True,2,42,645),(True,1,False,2,105,725),
        (False,0,True,3,42,78),(False,0,False,2,105,913),
        (False,1,True,2,42,769),(False,1,False,2,105,983),
    ):
        N,cols,d0=test_matrix(f,a,h,p,t,ga)
        assert N==n and len(cols)==n and d0==d
        print('nonzero coprime projection minor',f,a,h,ga,N,d0,'columns',cols,flush=True)
    print('all eight exact finite-diagonal projections certified nonzero',flush=True)

if __name__=='__main__':
    main()

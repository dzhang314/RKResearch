"""All affine Gauss contacts at an ordinary eighth or penultimate clock."""
from pathlib import Path
from sympy import isprime
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-eight-shared-gauss-one-front",
            "sdirk-eight-silent-one-eight-coprime-one-front-terminal",
            "sdirk-eight-silent-one-eight-coprime-one-front-finite",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from rear_gauss_fibers import test,root_consts

# Literal front star?, active slot 0=physical2 or 1=physical3;
# rear star?, Gaussian position, good prime/sqrt(1/2), number of
# all retained components at each of four lifts.
PHASES=[
    (True,0,True,9,1129,203,35),
    (True,0,False,9,1129,203,39),
    (True,0,False,8,1129,203,37),
    (True,1,True,9,1559,529,33),
    (True,1,False,9,1129,203,33),
    (True,1,False,8,1129,203,28),
    (False,0,True,9,1559,529,23),
    (False,0,False,9,1559,529,21),
    (False,0,False,8,1559,529,14),
    (False,1,True,9,1129,203,17),
    (False,1,False,9,1129,203,21),
    (False,1,False,8,1129,203,20),
]

def main():
    assert root_consts(1129)==[100,214,916,1030]
    assert root_consts(1559)==[564,593,967,996]
    for f,j,rear,hit,p,t,n in PHASES:
        assert isprime(p) and (2*t*t-1)%p==0
        v=test(f,j,rear,hit,p,t)
        assert v==(n,)*4
        print('verified coprime rear Gauss phase',f,j,rear,hit,p,t,v,flush=True)
    print('all twelve rear Gauss orientations excluded',flush=True)

if __name__=='__main__':
    main()

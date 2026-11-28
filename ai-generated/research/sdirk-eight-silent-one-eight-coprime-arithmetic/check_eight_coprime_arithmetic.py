"""Complete coprime live arithmetic rear validation, independent of exploratory scans."""
from pathlib import Path
from sympy import isprime
import sys

root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-eight-coprime-star",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from eight_arithmetic_fibers import check_reg
from eight_arithmetic_contact import check_bad_rank
from eight_arithmetic_gauss import gamma_mode,verify_r

def main():
    p,t=1097,345
    assert isprime(p) and (2*t*t-1)%p==0
    for f,n,contact in ((True,5,(1,2,2,3,4,4,8,12)),
                        (False,7,(1,1,2,2,3,4,5,8,10))):
        assert check_reg(f,p,t)==(n,)*4
        assert check_bad_rank(f,p,t)==contact
        for mode,deg in enumerate((5,12,9)):
            assert len(gamma_mode(f,mode)[0])==deg+1
            assert verify_r(f,mode,p,t)==(1,1,2)
        print('complete arithmetic front phase excluded',f,flush=True)
    print('all complete eight-active coprime arithmetic modes excluded',flush=True)

if __name__=='__main__':
    main()

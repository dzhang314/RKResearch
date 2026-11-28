"""Full early-rank-two ordinary hole5, actual silent 2/3, star front arithmetic rear."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-rank-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole5_rank
from h5_regular_modular import fiber
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out=[fiber(True,False,z,p,t) for z in (2,3)]
    assert out==[21,20]
    print('regular ordinary hole5 star-front arithmetic-rear actual literal 2/3 excluded',flush=True)

if __name__=='__main__':
    main()

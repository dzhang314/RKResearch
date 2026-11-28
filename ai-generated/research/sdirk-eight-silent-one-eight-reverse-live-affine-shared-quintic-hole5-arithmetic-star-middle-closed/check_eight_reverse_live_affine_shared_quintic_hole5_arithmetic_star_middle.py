"""Full ordinary hole5 arithmetic front/star rear, physical silent 6 and 7."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for name in ('sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-arithmetic-fourth-closed',
             'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-star-middle-closed'):
    sys.path.append(str(root/name))
import check_eight_reverse_live_affine_shared_quintic_hole5_arithmetic_arithmetic_fourth
import check_eight_reverse_live_affine_shared_quintic_hole5_star_star_middle
from h567_af_star_modular import test
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out=test(p,t)
    assert out==(13,[]),out
    print('regular corrected ordinary hole5 arithmetic-front star-rear actual silent sixth and seventh excluded',flush=True)

if __name__=='__main__':
    main()

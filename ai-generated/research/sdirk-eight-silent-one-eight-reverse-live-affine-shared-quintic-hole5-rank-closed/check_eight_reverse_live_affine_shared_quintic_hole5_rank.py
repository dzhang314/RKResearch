"""Complete early rank-loss ordinary hole5 with actual silent 2/3/4/6/7/8."""
from pathlib import Path
from itertools import product
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole_literal
from h5_rank_check import rank_mode
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    for f,r in product((True,False),(True,False,None)):
        assert rank_mode(f,r,p,t)==(2 if f else 1)
    print('all corrected ordinary hole5 early rank-loss placements excluded',flush=True)

if __name__=='__main__':
    main()

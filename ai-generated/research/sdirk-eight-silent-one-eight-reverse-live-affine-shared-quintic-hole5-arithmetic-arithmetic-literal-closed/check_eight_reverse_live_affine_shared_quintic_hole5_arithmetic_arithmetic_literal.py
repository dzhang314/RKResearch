"""Full independent regular arithmetic-front/rear actual silent 2 and 3."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-star-literal-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole5_arithmetic_star_literal
from h5_artharth_modular import test
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    outputs=[test(z,p,t) for z in (2,3)]
    assert outputs==[(5,[]),(9,[])],outputs
    print('regular corrected ordinary hole5 arithmetic-front arithmetic-rear literal 2 and literal 3 excluded',flush=True)

if __name__=='__main__':
    main()

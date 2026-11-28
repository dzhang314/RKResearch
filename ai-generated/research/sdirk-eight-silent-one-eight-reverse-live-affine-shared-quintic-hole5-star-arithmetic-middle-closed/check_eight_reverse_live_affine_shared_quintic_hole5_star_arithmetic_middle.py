"""Complete ordinary hole5, true star/arithmetic front/rear, extra silent sixth/seventh."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-star-middle-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole5_star_star_middle
from h567_arithmetic_modular import test
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out=[test(cubic,p,t) for cubic in (False,True)]
    assert out==[[(3,[]),(1,[])],[(7,[])]],out
    print('regular ordinary hole5 star-front arithmetic-rear actual silent sixth and seventh excluded',flush=True)

if __name__=='__main__':
    main()

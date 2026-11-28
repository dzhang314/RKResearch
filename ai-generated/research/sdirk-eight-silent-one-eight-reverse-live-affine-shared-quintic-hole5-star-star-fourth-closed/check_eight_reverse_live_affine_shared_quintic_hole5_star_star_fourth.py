"""Complete actual ordinarily silent fourth, star front and star ordinary rear."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-star-literal-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole5_star_star_literal
from h54_star_modular import test
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out=[test(cubic,p,t) for cubic in (False,True)]
    assert out==[(5,[]),(13,[])],out
    print('regular ordinary hole5 star-front star-rear actual literal fourth excluded',flush=True)

if __name__=='__main__':
    main()

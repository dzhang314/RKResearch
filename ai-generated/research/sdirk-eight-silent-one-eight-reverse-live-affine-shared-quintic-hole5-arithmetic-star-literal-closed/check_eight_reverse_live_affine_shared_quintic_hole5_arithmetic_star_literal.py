"""Complete true arithmetic-front / star-rear literal 2 and literal 3."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-star-literal-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole5_star_star_literal
from h5_arthfront_modular import test
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    output=[test(z,p,t) for z in (2,3)]
    assert output==[(8,[]),(5,[])],output
    print('regular corrected ordinary hole5 arithmetic-front star-rear literal 2 and literal 3 excluded',flush=True)

if __name__=='__main__':
    main()

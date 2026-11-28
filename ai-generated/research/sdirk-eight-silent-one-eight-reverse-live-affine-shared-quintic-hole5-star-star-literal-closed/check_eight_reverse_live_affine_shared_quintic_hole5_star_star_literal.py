"""All true star-front/star-rear literal hole5 branches, with exact degree drops."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for name in ('rank','star-arithmetic-literal'):
    sys.path.append(str(root/f'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-{name}-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole5_star_arithmetic_literal
from h5_star_modular import test
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    output=[test(z,cubic,p,t) for z in (2,3) for cubic in (False,True)]
    assert output==[(4,[]),(10,[]),(10,[]),(12,[])],output
    print('regular ordinary hole5 star-front star-rear actual literal 2/3 excluded',flush=True)

if __name__=='__main__':
    main()

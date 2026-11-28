"""Regular corrected hole5, true star front/rear, actual silent sixth or seventh."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for name in ('star-star-literal','star-arithmetic-fourth'):
    sys.path.append(str(root/f'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-{name}-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole5_star_arithmetic_fourth
from h567_star_modular import test
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out=[test(cu,p,t) for cu in (False,True)]
    assert out==[[(3,[]),(1,[])],[(7,[])]],out
    print('regular ordinary hole5 star-front star-rear actual silent sixth and seventh excluded',flush=True)

if __name__=='__main__':
    main()

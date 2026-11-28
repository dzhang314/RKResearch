"""Full regular true arithmetic front/rear and actual silent fourth."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for name in ('sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-arithmetic-literal-closed',
             'sdirk-eight-silent-one-eight-reverse-live-star-arithmetic5-closed'):
    sys.path.append(str(root/name))
import check_eight_reverse_live_affine_shared_quintic_hole5_arithmetic_arithmetic_literal
from h54_af_ar_modular import test
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out=test(p,t)
    assert out==(14,[]),out
    print('regular ordinary hole5 arithmetic-front arithmetic-rear true silent fourth excluded',flush=True)

if __name__=='__main__':
    main()

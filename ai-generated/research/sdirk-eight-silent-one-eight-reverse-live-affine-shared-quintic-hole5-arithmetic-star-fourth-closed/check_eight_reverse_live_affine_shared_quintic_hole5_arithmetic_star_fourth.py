"""Regular corrected hole5 arithmetic front/star rear, true silent fourth."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-star-literal-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole5_arithmetic_star_literal
from h54_af_star_modular import test
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out=test(p,t)
    assert out==(11,[]),out
    print('regular ordinary hole5 arithmetic-front star-rear true silent fourth excluded',flush=True)

if __name__=='__main__':
    main()

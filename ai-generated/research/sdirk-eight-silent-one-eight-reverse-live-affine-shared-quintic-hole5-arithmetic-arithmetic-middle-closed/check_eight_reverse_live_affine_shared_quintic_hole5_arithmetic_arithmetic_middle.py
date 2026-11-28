"""Regular corrected ordinary hole5, actual silent sixth or seventh, arithmetic front/rear."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for name in ('sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-star-middle-closed',
             'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-arithmetic-middle-closed'):
    sys.path.append(str(root/name))
import check_eight_reverse_live_affine_shared_quintic_hole5_arithmetic_star_middle
import check_eight_reverse_live_affine_shared_quintic_hole5_star_arithmetic_middle
from h567_af_ar_modular import test
from h567_af_ar_projection import project
from audit_mass_free_rows import audit
from sympy import isprime

def main():
    audit()
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out=test(p,t)
    assert out==(21,[]),out
    assert project()[0].degree()==4181
    print('regular corrected ordinary hole5 arithmetic-front arithmetic-rear true silent sixth and seventh excluded',flush=True)

if __name__=='__main__':
    main()

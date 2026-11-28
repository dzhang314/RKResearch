"""Complete regular corrected ordinary hole5, arithmetic front and true silent eighth."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for name in ('sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-arithmetic-middle-closed',
             'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-silent-eighth-closed'):
    sys.path.append(str(root/name))
import check_eight_reverse_live_affine_shared_quintic_hole5_arithmetic_arithmetic_middle
import check_eight_reverse_live_affine_shared_quintic_hole5_star_silent_eighth
from h58_af_modular import test
from h58_af_projection import project
from h58_af_leading import degree_locus,test_locus,rem
from audit_silent8_mass_free import audit
from flint import nmod_poly
from sympy import isprime

def check_leading():
    p,t=1129,203
    L,_,_=degree_locus()
    d=test_locus(p,t)
    assert L.degree()==3 and d==nmod_poly([79,620,24,1],p)
    return L,d

def main():
    audit()
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out,bad=test(p,t)
    L,d=check_leading()
    M,_,_=project()
    assert M.degree()==3153 and not rem(M,L)
    assert out==22 and bad==[('Y lead',(3,1),str(d))],(out,bad)
    print('regular corrected ordinary hole5 arithmetic-front true silent eighth excluded',flush=True)

if __name__=='__main__':
    main()

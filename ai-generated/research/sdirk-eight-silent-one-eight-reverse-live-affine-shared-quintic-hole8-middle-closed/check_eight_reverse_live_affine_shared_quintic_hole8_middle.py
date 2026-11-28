"""Complete ordinary hole8 with actual ordinarily silent 5, 6 or 7."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for d in (
    'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole8-literal-closed',
    'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed',
):
    sys.path.append(str(root/d))
import check_eight_reverse_live_affine_shared_quintic_hole8_literal
import check_eight_reverse_live_affine_shared_quintic_hole4_middle
from hole_quintic_rank import rank_loss
from h8m_modular import mode
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    for f in (True,False):
        assert len(rank_loss(f,p,t))==(2 if f else 1)
        assert mode(f,p,t)==(28 if f else 17)
    print('ordinary hole8 with actual silent 5, 6 or 7 excluded before later assignment',flush=True)

if __name__=='__main__':
    main()

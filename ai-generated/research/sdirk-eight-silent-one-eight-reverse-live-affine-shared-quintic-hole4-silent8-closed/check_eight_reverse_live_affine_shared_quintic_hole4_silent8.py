"""Full ordinary hole4 with actual ordinarily silent eighth, both literal front phases."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole4_middle
from hole_quintic_rank import rank_loss
from h8_modular import check
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    for f in (True,False):
        assert len(rank_loss(f,p,t))==(2 if f else 1)
        assert check(f,p,t)==(28 if f else 10)
    print('ordinary hole4 plus actual silent8: both front phases excluded before actual sixth',flush=True)

if __name__=='__main__':
    main()

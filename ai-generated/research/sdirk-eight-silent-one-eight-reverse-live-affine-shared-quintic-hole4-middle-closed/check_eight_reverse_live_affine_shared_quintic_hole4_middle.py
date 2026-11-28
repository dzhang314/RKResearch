"""Full corrected ordinary-hole4 closure under actual silent stage 5, 6, or 7."""
from pathlib import Path
from itertools import product
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole_literal
from hole_quintic_rank import rank_loss
from hm_modular import mode
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    for f in (True,False):
        assert len(rank_loss(f,p,t))==(2 if f else 1)
    n=[mode(f,r,p,t) for f,r in product((True,False),repeat=2)]
    assert n==[21,36,15,22]
    print('ordinary hole4 plus actual silent 5, 6, or 7: excluded, complete components',n,flush=True)

if __name__=='__main__':
    main()

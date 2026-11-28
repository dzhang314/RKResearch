"""Corrected actual ordinary eighth hole with literal silent 2, 3 or 4."""
from pathlib import Path
from itertools import product
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole_literal
from hole_quintic_rank import rank_loss
from h8l_modular import check
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    for f in (True,False):
        assert len(rank_loss(f,p,t))==(2 if f else 1)
    n=[check(f,z,p,t) for f,z in product((True,False),(2,3,4))]
    assert n==[9,11,14,9,7,9]
    print('actual ordinary hole8 plus literal silent 2/3/4 excluded, components',n,flush=True)

if __name__=='__main__':
    main()

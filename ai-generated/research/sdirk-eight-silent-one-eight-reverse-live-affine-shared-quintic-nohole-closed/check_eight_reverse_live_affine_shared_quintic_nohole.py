"""Replay all actual ordinarily silent placements for the shared quintic without an ordinary hole."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic23-closed'))
# The companion only registers the published exact arithmetic dependencies.
import check_eight_reverse_live_affine_coprime_quartic23
from sympy import isprime
from no_hole_quintic_model import literal_positions
from no_hole_quintic_recovery import middle,eighth

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    for front in (True,False):
        n=2 if front else 1
        for rear in (True,False):
            assert literal_positions(front,rear,p,t)==n
            assert middle(front,rear,p,t)==n
        assert eighth(front,p,t)==n
    print('all 26 actual affine shared-quintic no-ordinary-hole placements excluded',flush=True)

if __name__=='__main__':
    main()

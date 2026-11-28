"""Exact ordinary-hole agreement, early rank loss, and literal fourth-hole closures."""
from pathlib import Path
from itertools import product
import sys

root=Path(__file__).resolve().parent.parent
for d in (
  'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-nohole-closed',
  'sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic5-closed',
  'sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed',
):
    sys.path.append(str(root/d))
import check_eight_reverse_live_affine_shared_quintic_nohole as agreement
import check_eight_reverse_live_affine_coprime_quartic5
from hole_quintic_rank import rank_loss,Ls
from flint import fmpq, fmpq_poly
from hole4_modular import fibers
from sympy import isprime

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    for j in range(4):
        read=sum((2*i+1)*sum(fmpq(c,j+k+1) for k,c in enumerate(F))*fmpq_poly(list(F))
                 for i,F in enumerate(Ls))
        assert read==fmpq_poly([0]*j+[1])
    agreement.main()
    print('shared-root ordinary-hole agreement case reuses all exact amplitude-matched fibers')
    for f in (True,False):
        assert len(rank_loss(f,p,t))==(2 if f else 1)
    counts=[fibers(f,r,z,p,t) for f,r,z in product((True,False),(True,False),(2,3))]
    assert counts==[10,12,15,12,5,9,8,10]
    print('all eight fourth-hole corrected literal orientations excluded, complete components',counts,flush=True)

if __name__=='__main__':
    main()

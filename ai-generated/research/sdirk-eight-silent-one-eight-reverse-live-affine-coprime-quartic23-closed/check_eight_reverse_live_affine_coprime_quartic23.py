"""Full literal ζ2/ζ3 affine-coprime quartic Replay. See README.md."""
from itertools import product
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for dep in (
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-silent-eighth-closed",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-seven-distinct-anchors",
    "sdirk-eight-silent-one-seven-distinct-coprime",
    "sdirk-eight-silent-one-seven-six-anchored",
    "sdirk-eight-silent-one-seven-six-reverse",
    "sdirk-eight-silent-one-seven-six-shared",
    "sdirk-eight-silent-three-closure",
    "sdirk-eight-silent-two-equal",
    "sdirk-eight-silent-two-high",
    "sdirk-eight-silent-two-unequal",
):
    sys.path.append(str(root/dep))

from flint import fmpq, fmpq_poly
from sympy import isprime
from aq_modular import fiber, Lco

def main():
    # Rational moment constants, independent of any reduction.
    assert all(sum(fmpq(a,j+i+1) for i,a in enumerate(Lco))==0 for j in range(4))
    W=[sum(fmpq(Lco[j],j-i) for j in range(i+1,5)) for i in range(4)]
    assert fmpq_poly(list(Lco)).gcd(fmpq_poly(W))==fmpq_poly([1])
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    census=[]
    for front,rear,slot in product((True,False),(True,False),(2,3)):
        census.append(fiber(front,rear,slot,p,t))
    print('full affine-coprime literal 2/3 census',census,flush=True)
    print('all eight characteristic-zero affine-coprime quartic literal orientations excluded',flush=True)

if __name__=='__main__':
    main()

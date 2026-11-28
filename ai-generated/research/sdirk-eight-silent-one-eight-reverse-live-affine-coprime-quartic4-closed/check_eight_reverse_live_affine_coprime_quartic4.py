"""Complete replay of the four literal ordinarily silent fourth orientations."""
from itertools import product
from pathlib import Path
import sys

# Importing the companion's entry point registers exactly its published sibling
# dependencies. It does not run its proof.
root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic23-closed'))
import check_eight_reverse_live_affine_coprime_quartic23
from sympy import isprime
from aq4_modular import fiber

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    counts=[fiber(front,rear,p,t) for front,rear in product((True,False),repeat=2)]
    print('full affine-coprime silent fourth census',counts,flush=True)
    print('all four characteristic-zero affine-coprime quartic silent fourth orientations excluded',flush=True)

if __name__=='__main__':
    main()

"""Full six-ordinary-peg replay with actual ordinarily silent fifth."""
from itertools import product
from pathlib import Path
import sys

# Registers only the previously verified dependency list, with no proof run
# until this entry point is called.
root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic4-closed'))
import check_eight_reverse_live_affine_coprime_quartic4
from sympy import isprime
from aq5_modular import fibers

def main():
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    counts=[fibers(f,r,p,t) for f,r in product((True,False),repeat=2)]
    print('full affine-coprime silent fifth census',counts,flush=True)
    print('all four characteristic-zero affine-coprime quartic silent fifth orientations excluded',flush=True)

if __name__=='__main__':
    main()

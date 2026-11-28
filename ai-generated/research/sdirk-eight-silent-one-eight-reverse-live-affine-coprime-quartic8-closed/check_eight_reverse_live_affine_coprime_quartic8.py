"""Complete actual silent-eighth affine-coprime quartic exclusion."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
for d in (
  'sdirk-eight-silent-one-eight-reverse-live-affine-coprime-quartic5-closed',
  'sdirk-eight-silent-one-eight-reverse-live-arithmetic-silent-eighth-closed',
  'sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed',
):
    sys.path.append(str(root/d))
import check_eight_reverse_live_affine_coprime_quartic5
from aq8_projection import res23
from aq8_exception import special
from aq8_fibers import all_mod
from sympy import symbols, expand, isprime, resultant

def main():
    y,a,b,c,d,e,f,h=symbols('y a b c d e f h')
    assert expand(res23(c,b,a,h,f,e,d)-resultant(a*y**2+b*y+c,d*y**3+e*y**2+f*y+h,y))==0
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    for front in (True,False):
        assert special(front,p,t)==[4,4,4]
        all_mod(front,p,t)
    print('both actual silent-eighth affine-coprime quartic front phases excluded',flush=True)

if __name__=='__main__':
    main()

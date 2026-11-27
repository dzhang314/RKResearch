"""Replay the exact high-active equal invisible-tag chart packets."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal"):
 sys.path.insert(0,str(root/dep))
from itertools import product
from equal_detected import K,L4,ends
from equal_four import main as gauss_tail
from gauss_triple import check as triple
from seven_distinct import run
from midpoint import midpoint
from shared_proxy import transfer
from silent_eighth import twofront as two_front_silent, half as half_silent

def two_front_tail():
 for f,i,t in product((True,False),(0,1),(True,False)):
  a,b,_=ends(f,1);X,Y=(a,b) if i==0 else (b,a)
  g=K.one/(1+X);x=1-g;u=X-Y
  d=x-g*(2-u if t else 2*u)
  assert L4(g) and L4(d)
 print('Two canceled non-Gauss front groups: all eight literal third-tail choices excluded')

if __name__=='__main__':
 triple()
 gauss_tail()
 two_front_tail()
 two_front_silent()
 run()
 for f in (True,False):
  midpoint(f)
  half_silent(f)
  transfer(f)

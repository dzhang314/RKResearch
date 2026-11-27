"""Exact one-invisible undetected seven-active and attached six-active replays."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal"):
 sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from seven_distinct import tests
from seven_repeat import check_seven
from six_attached import test
from equal_undetected_front import direct_units,five_output
from equal_four import main as gauss_front
if __name__=='__main__':
 gauss_front()
 for p,t in ((1103,161),(1129,203)):
  assert isprime(p) and (2*t*t-1)%p==0
 for f in (True,False):
  assert direct_units(f,1129,203) and five_output(f,1129,203)
 for f,r,e in product((True,False),(True,False),(1,-1)):
  assert check_seven(f,r,e,1103,161)
  print('seven active with repeat, and six active with attached active eighth, excluded',f,r,e,flush=True)
 for f,r in product((True,False),(True,False)):
  assert tests(f,r,1129,203)
  print('seven distinct active clocks excluded',f,r,flush=True)
 for f,e in product((True,False),(1,-1)):
  assert test(f,e,1103,161)
  print('six active with attached silent eighth excluded',f,e,flush=True)

"""Complete six-active single-invisible case, exact finite replays."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-one-row"):
 sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from six_separate import check_separate
from six_front_clock import z6,z7,z8
from early_repeated import raw,fifth_silent
from early_fourth import check as fourth_silent
if __name__=='__main__':
 assert isprime(1129) and isprime(1103)
 assert (2*203*203-1)%1129==0 and (2*161*161-1)%1103==0
 for f in (True,False):
  assert check_separate(f,1129,203)
  print('virtual seventh with silent eighth',f,flush=True)
 for f,b,a in product((True,False),(True,False),(True,False)):
  assert z6(f,b,a,1103,161)
  assert z7(f,b,a,1103,161)
  print('late silent at literal front, placements six and seven',f,b,a,flush=True)
 for f,a in product((True,False),(True,False)):
  assert z8(f,a,1103,161)
  print('late silent at literal front, placement eight',f,a,flush=True)
 for r,e in product((True,False),(1,-1)):
  T,H=raw(r,e);D=T.factor_list()[1]
  assert sorted((q.degree(),m) for q,m in D)==([(9,1)] if r else [(1,1),(8,1)])
  for M,k in D:
   for f in (True,False):
    assert fifth_silent(f,r,e,M.monic(),H,1103,161)
    assert fourth_silent(f,r,e,M.monic(),H,1103,161)
    print('both early silent placements with terminal double excluded',f,r,e,M.degree(),flush=True)

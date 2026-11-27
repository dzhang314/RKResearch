"""Replay the final two low-active equal-tag scalar exclusions exactly."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal"):
 sys.path.insert(0,str(root/dep))
from equal_undetected_front import check,ev
from equal_detected import h4,Z
from variable_atlas import K
if __name__=="__main__":
 for front in (True,False):
  H=h4(front)
  value=H.evaluate(Z,K.one)
  assert value == (-K.one/2 if front else -29*K.one/4+21*K.unit/2)
  assert value
  for H0,F,data,R,A in check(front):
   _,_,s,*_=data
   assert s!=F(1) and ev(R,F(1))
  print("Both literal silent-clock placements excluded, phase",front)

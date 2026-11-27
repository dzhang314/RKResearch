"""Offline replay, using Python 3, SymPy 1.14.0 and python-flint 0.9.0."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for package in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
                "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal"):
 sys.path.insert(0,str(root/package))
import equal_detected, equal_six, equal_five, equal_four, equal_undetected_front
from gauss_triple import check as triple
if __name__=="__main__":
 triple()
 equal_detected.run()
 for f,b,e in equal_six.product((True,False),(True,False),(1,-1)):
  equal_six.away(f,b,e)
 for f in (True,False):
  equal_six.visit(f,lambda F,s,c:1/(1+s),True)
  for i in (0,1):
   a=equal_six.ends(f,1)[i]
   equal_six.visit(f,lambda F,s,c:1/(1+c(a)),False)
 equal_five.main()
 equal_four.main()
 equal_undetected_front.main()

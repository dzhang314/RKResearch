"""Exact finite-profile replay in the sibling source tree."""
import sys
from pathlib import Path
from itertools import product

root=Path(__file__).resolve().parent.parent
for p in sorted(root.glob("sdirk-eight-*")):
 if p.is_dir() and p.resolve()!=Path(__file__).resolve().parent:sys.path.append(str(p))

from nonliteral_fourth_content import contents,verify

if __name__=='__main__':
 for f,i in product((True,False),(0,1)):assert contents(f,i)
 for f,i,r in product((True,False),(0,1),(True,False)):assert verify(f,i,r)
 print('true single nonliteral fourth finite clock/weight chart: 8')

"""Reproduce the exact degree and both separately lower-degree branches."""
import sys
from pathlib import Path
from itertools import product

ROOT=Path(__file__).resolve().parent.parent
for p in sorted(ROOT.glob("sdirk-eight-*")):
 if p.is_dir() and p.resolve()!=Path(__file__).resolve().parent:sys.path.append(str(p))

from check_degree import leading
from leading_branch import check as tail_zero
from fourth_drop_branch import check4 as fourth_zero
from verify_crt import check,rec

if __name__=='__main__':
 assert set(sys.argv[1:])<= {'--crt'}
 for f,i in product((True,False),(0,1)):
  assert leading(f,i)
  assert not tail_zero(f,i,1103,161)
  assert not fourth_zero(f,i,1103,161)
  if '--crt' in sys.argv:assert check(f,i,rec(f,i))
 print('exact no-front arithmetic degree and lower-degree exclusions: 4 8')

"""Complete guarded replay of the solely transported nonliteral physical fourth."""
import sys
from pathlib import Path
from itertools import product
root=Path(__file__).resolve().parent.parent
for p in sorted(root.glob('sdirk-eight-*')):
 if p.is_dir() and p.resolve()!=Path(__file__).resolve().parent:sys.path.append(str(p))

from nonliteral_fourth_content import contents
from nonliteral_fourth_crt import reconstruct,packed,resultant_mod
from nonliteral_fourth_closed_fibers import finite_checks
from shared_silent8_projection import red_e

def check(f,i,r):
 assert contents(f,i)
 H=reconstruct(f,i,r);W=packed(f,i,r)
 d=(256 if f else 269) if r else (1328 if f else 1393)
 p,t=1103,161
 assert 2*t*t%p==1
 M=resultant_mod(W,p,2*t)
 assert H.degree()==M.degree()==d and red_e(H,p,t)==M
 assert not finite_checks(f,i,r,H.monic(),None,['tight'],p,t)
 print('exact nonliteral fourth orientation closes',f,i,r,H.degree(),p,flush=True)
 return True

if __name__=='__main__':
 for f,i,r in product((True,False),(0,1),(True,False)):assert check(f,i,r)
 print('complete genuinely nonliteral fourth exclusions: 8')

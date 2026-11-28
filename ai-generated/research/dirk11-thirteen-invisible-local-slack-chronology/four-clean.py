#!/usr/bin/env python3
"""Old quartic nonvanishing in the common exact degree-24 ordinary model."""
import argparse
import hashlib
from pathlib import Path
import sys
a=argparse.ArgumentParser()
a.add_argument('repo',type=Path)
a.add_argument('--prime',type=int,default=103)
o=a.parse_args()
r=o.repo.resolve()/'ai-generated'/'research'
src=r/'dirk11-thirteen-invisible-six-alpha-two-live-cubic-beta-one'/'finite.py'
raw=src.read_bytes()
assert hashlib.sha256(src.with_name('ordinary.py').read_bytes()).hexdigest()==    '090065b8eefd799592a0be1d29a28f15002380ef759efb3875cb4d1f6038530e'
lib=r/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py'
assert hashlib.sha256(lib.read_bytes()).hexdigest()==    'a9a028da203d86d336a338389465a970540f7e356af304d377cb0288fc0e9604'

assert hashlib.sha256(raw).hexdigest()=='9e4f0bca8d718f8fdef324a902cdbfb606923ba56fd1443a617a1364c9294dab'
base=raw.decode()
start='    j,l0,yl0,l1='
end="if __name__=='__main__':\n"
assert base.count(start)==base.count(end)==1
s=base[:base.index(start)]+'''    old=Ring("old ordinary",K,R3[:-1])
    y=old.gen()
    l0=ev([old.to(c) for c in L0],y)
    assert l0*l0.inv()==1
    print("Old L0 is a unit in the full degree24 x 3 ordinary algebra",p,flush=True)
'''+base[base.index(end):]
assert 'Cdet.inv()' not in s and 'first_b' not in s
sys.argv=[str(src),'--research',str(r),'--prime',str(o.prime)]
exec(compile(s,str(src),'exec'),{'__name__':'__main__','__file__':str(src)})

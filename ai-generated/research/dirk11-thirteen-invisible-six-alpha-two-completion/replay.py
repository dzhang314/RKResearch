#!/usr/bin/env python3
"""The common four-clean ordinary algebra, with a separate literal adjacent read."""
import argparse
import hashlib
from pathlib import Path
import sys
p=argparse.ArgumentParser()
p.add_argument('repo',type=Path)
p.add_argument('--prime',type=int,default=103)
p.add_argument('--count',choices=['adjacent','middle'],default='adjacent')
o=p.parse_args()
r=o.repo.resolve()/'ai-generated'/'research'
src=r/'dirk11-thirteen-invisible-six-alpha-two-live-cubic-beta-one'/'finite.py'
def verify(p, h):
    raw=p.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==h,p
    return raw.decode()
s=verify(src,'9e4f0bca8d718f8fdef324a902cdbfb606923ba56fd1443a617a1364c9294dab')
verify(src.with_name('ordinary.py'),'090065b8eefd799592a0be1d29a28f15002380ef759efb3875cb4d1f6038530e')
verify(r/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py',
       'a9a028da203d86d336a338389465a970540f7e356af304d377cb0288fc0e9604')
verify(r/'dirk11-thirteen-invisible-six-early-profile-census'/'project.py',
       '0ba9d57bb50ec53700c6d735033777fe145c80e9edd4f87ba8e8e2c840de9fcd')
if o.count=='adjacent':
    start='    # A and D are the two coefficients of the affine Q5/W0'
    end='    vv=ev(L0,v)'
    assert s.count(start)==s.count(end)==1
    s=s[:s.index(start)]+s[s.index(end):]
    a='        test.inv()\n'
    b='    def singular():\n'
    assert s.count(a)==s.count(b)==1
    pos=s.index(a)
    s=s[:pos]+'''        # Here B immediately follows V in literal reverse order. Do not
        # reconstruct a third ghost, force d_B=0 or use the middle gate.
        dV=ev(D,vs)
        U=plus(scale(M,vvT),scale(rr3,-dV))
        E=plus(scale(D,vvT),scale(list(map(T.to,L0)),-dV))
        B=T.to(bb)
        uv=ev(U,B); em=ev(E,B); Jb=first_b(U,B)
        assert Jb==test
        diff=B-vs
        adj=(diff*bs*uv-Jb)*em-diff*Jb*uv
        adj.inv()
        print('adjacent rank72: literal fifth commutator signal is a unit',p,flush=True)
'''+s[s.index(b):]
    assert 'Cdet.inv()' not in s and 'test.inv()' not in s
sys.argv=[str(src),'--research',str(r),'--prime',str(o.prime)]
exec(compile(s,str(src),'exec'),{'__name__':'__main__','__file__':str(src)})

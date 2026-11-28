#!/usr/bin/env python3
"""Replay the literal late-cut arithmetic and its additional repeat guards."""
import argparse
import hashlib
from pathlib import Path
from runpy import run_path
import sys
ap=argparse.ArgumentParser()
ap.add_argument('repo',type=Path)
ap.add_argument('--prime',type=int,default=103)
o=ap.parse_args()
r=o.repo.resolve()/'ai-generated'/'research'
p=r/'dirk11-thirteen-invisible-six-paid'/'replay.py'
arith=r/'dirk11-thirteen-fourth-clean'/'replay_mod101.py'
assert hashlib.sha256(p.read_bytes()).hexdigest()==    'f97b01821a32d69ebf01c9cb5d2d7d656f5f5c101a53809485c8e90f82bb9420'
assert hashlib.sha256(arith.read_bytes()).hexdigest()==    'd76bf66f2e1be5cd015b5f52644009ae0a86c72605c5ab598f55111f9a38704b'

sys.argv=[str(p),'--prime',str(o.prime),'--arithmetic',str(arith)]
v0=run_path(str(p),run_name='__main__')
u,v,w,a,b,qa=(v0[k]for k in ('u','v','w','a','b','qa'))
geo,cast,dot,two_taps=(v0[k]for k in ('geometry','cast','dot','two_taps'))
m=geo(u,v,w)
for r in (u,v,w):
    z=w-m['lam'](r)
    assert z*z.inv()==1
print('All three pre-fourth repeat coefficients are units.',flush=True)
u,v,w,a,b=cast(qa,u,v,w,a,b)
m=geo(u,v,w)
K,J,L,lam,e,q0,h0,h=(m[k]for k in ('K','J','L','lam','e','q0','h0','h'))
taps=two_taps(w,a,K(a)-qa,J(a)-lam(a)*qa)
chi=(dot(taps,[w*w,a*a])-L(a)-q0(a)*qa)/(h(a)-h0(a)*qa)
R=lambda r:q0(r)-chi*h0(r)
for r in (u,v,w,a):
    z=(w+a)*lam(r)-w*a+R(r)
    assert z*z.inv()==1
print('All four pre-fifth repeat coefficients are units in the entire rank240 algebra.',flush=True)

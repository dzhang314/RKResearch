#!/usr/bin/env python3
"""Replay the first primitive pin alone in every frozen finite old model."""
import argparse
import hashlib
import sys
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
parser.add_argument('--case',choices=['all','finite','F1','F2','Fn'],default='all')
args=parser.parse_args()
base='dirk11-thirteen-invisible-six-alpha-one-beta-zero-'
sources=[
 ('finite',base+'finite-contacts',
  '847c63a0dde571940145b62d20bedb5df1b0b00abe7004788ba60b95e60f5261',
  [['m1'],['mY2'],['contact'],['Fn-loss']]),
 ('F1',base+'alternate-f1',
  '8ad9396ece9684040108275e7dfc224786e6cc0140ee281228c8052e0276fa1c',[[]]),
 ('F2',base+'alternate-f2',
  'f9386e78465d38dd12cf4d3c742473159ad05466c4592bc70bfac2bc51957663',[[]]),
 ('Fn',base+'alternate-fn',
  'eab8a0b05f98e798c7be405b137008f8887004da8fa1284acd294b71526e309e',
  [['H3'],['H5']]),
]
updates={
 'hbq=ev(U,b)*ev(IQ,b)-b*jB*ev(Lq,b)\n':'',
 'assert hv.degree<=2 and hbq.degree<=2':'assert hv.degree<=2',
 'rows=[pin(hv),pin(hbq)]':'rows=[pin(hv)]',
}
for name,pkt,digest,cases in sources:
    if args.case not in ('all',name):continue
    p=args.research/pkt/'proof.py'
    data=p.read_bytes()
    assert hashlib.sha256(data).hexdigest()==digest, str(p)
    source=data.decode()
    for a,b in updates.items():
        assert source.count(a)==1,(str(p),a)
        source=source.replace(a,b)
    assert 'hbq' not in source
    compiled=compile(source,str(p),'exec')
    for case in cases:
        print('First primitive pin only:',name,*case,flush=True)
        sys.argv=[str(p),*case]
        scope={'__name__':'__main__','__file__':str(p)}
        exec(compiled,scope)
        # Independently assert its full required rank even if a sibling's
        # print format or comparison were only for a combined population.
        assert len(scope['rows'])==1
        assert scope['rank'](scope['rows'])==scope['d']
        del scope
print('All selected first-pin ranks independently checked.',flush=True)

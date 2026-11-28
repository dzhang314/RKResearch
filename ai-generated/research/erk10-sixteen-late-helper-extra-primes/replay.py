#!/usr/bin/env python3
"""Rebuild and verify an alternative ERK10 16-stage family at 21 primes."""
from argparse import ArgumentParser
from math import isqrt
from pathlib import Path
import json,sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'erk10-sixteen-late-helper-primes'))
from build import make
from verify import values,compare

parser=ArgumentParser(description=__doc__)
parser.add_argument('--exponent',type=int,default=2)
parser.add_argument('--emit',type=Path)
o=parser.parse_args()
assert o.exponent >= 2
if o.emit:
    o.emit.mkdir(parents=True,exist_ok=True)
seeds=json.loads((HERE/'seeds.json').read_text())
assert len(seeds)==len({x['field'] for x in seeds})==21
for seed in seeds:
    p=seed['field']
    assert all(p%d for d in range(2,isqrt(p)+1))
    last=None
    for n in range(1,o.exponent+1):
        literal=make(seed,n)
        cnt,defect=values(literal)
        if n==1:assert defect==seed['next_failure_value']
        if n==2:assert defect==seed['next_failure_at_square']
        if last is not None:compare(last,literal)
        if o.emit:
            (o.emit/f'f{p}-power{n}.json').write_text(json.dumps(literal,indent=2)+'\n')
        print(p,n,cnt,defect)
        last=literal

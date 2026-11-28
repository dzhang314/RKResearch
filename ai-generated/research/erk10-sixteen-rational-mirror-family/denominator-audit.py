#!/usr/bin/env python3
from math import prod,isqrt,gcd
from pathlib import Path
import json
here=Path(__file__).resolve().parent
rounds=[]
for f,L in json.loads((here/'denominators.json').read_text()).items():
    m=int(json.loads((here/f).read_text())['denominator'])
    assert m==prod(int(p)**k for p,k in L.items())
    assert all(p>1 and all(p%d for d in range(2,isqrt(p)+1))for p in map(int,L))
    rounds.append({int(p)for p in L if int(p)>7})
    print(f,m,'unpaid prime support',sorted(rounds[-1]))
assert rounds[0]&rounds[1]=={11,13,19}
old=int(json.loads((here/'../erk10-sixteen-rational-mirror/tableau.json').read_text())['denominator'])
assert {p for p in rounds[0]&rounds[1] if old%p==0}=={11,13}
print('unpaid intersection of the three denominators: [11, 13]')

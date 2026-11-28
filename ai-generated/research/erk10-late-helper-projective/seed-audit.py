#!/usr/bin/env python3
"""The full projective reduction retains each independently checked prime seed."""
from projective import chart
from fractions import Fraction
from pathlib import Path
import json
S=Path(__file__).resolve().parent.parent/'erk10-sixteen-late-helper-primes/seeds.json'
for row in json.loads(S.read_text()):
    p=row['field'];a,b,h,z,d,e,xi=row['raw'][2:]
    f=Fraction(row['theta']);t=f.numerator*pow(f.denominator,-1,p)%p
    mask,seeds=chart(d,e,xi,p,True)
    assert (t,z,*sorted((a,b)))in seeds and (mask>>t)&1
    print(p,'retained actual theta,z,a,b residues',t,z,a,b)

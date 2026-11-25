#!/usr/bin/env python3
"""Uniform joint characteristic separation of *original unstrengthened* two indices."""
from math import gcd,prod
from pathlib import Path
import json,sys
base=Path(sys.argv[1]);c,q=[int(json.loads((base/('index_'+s+'.json')).read_text())['raw_hex'],16) for s in ['cubic','quartic']]
def xg(a,b):
 r,s,t,u=1,0,0,1;x,y=a,b
 while y:
    n,k=divmod(x,y);x,y=y,k;r,s=s,r-n*s;t,u=u,t-n*u
 if x<0:x,r,t=-x,-r,-t
 assert r*a+t*b==x
 return x,r,t
d,a,b=xg(c,q);assert d==2**2854*3**1522*5**960*7**333*11**730*13**144
assert abs(c)%d==abs(q)%d==0
C=prod(m for m,_ in json.loads((base/'cubic_global_components.json').read_text()));Q=prod(r['m'] for r in json.loads((base/'quartic_global_accepted.json').read_text()))
assert gcd(c,Q)==gcd(q,C)==gcd(C,Q)==1
print('Exact integer Bezout: gcd(original cubic index, original quartic index) = 2^2854*3^1522*5^960*7^333*11^730*13^144.')
print('Consequently no prime >13 can even survive both original coarse projection tests.')

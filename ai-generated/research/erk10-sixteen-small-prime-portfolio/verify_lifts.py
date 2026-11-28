#!/usr/bin/env python3
"""Independent exact replay of the higher-power portfolio literals."""
from audit import HERE,read,replay
import json
for p in (11,13,19,23):
 d,A,b=read(p);q=p
 for e in (2,3):
  j=json.loads((HERE/'literals'/('mod'+str(p)+'pow'+str(e)+'.json')).read_text())
  a,c,m=j['A'],j['b'],j['modulus']
  assert m==p**e and j['exponent']==e
  assert [[v%q for v in row]for row in a]==A and [v%q for v in c]==b
  n,x=replay(a,c,m,p)
  assert n==1205 and x==j['bush_failure'] and x%p==int(d['next_failure_value'])
  print(str(p)+'^'+str(e)+' compatible; 1205 ordinary rooted conditions and unit bush defect',x)
  A,b,q=a,c,m

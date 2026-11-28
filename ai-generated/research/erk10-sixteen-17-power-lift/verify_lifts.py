#!/usr/bin/env python3
"""Independent exact all-tree replay of each higher-power literal."""
from pathlib import Path
import sys,json
D=Path(__file__).resolve().parent
base=D.parent/'erk10-sixteen-f17'
sys.path.insert(0,str(base))
from verify import replay

def coeff(doc):
 return [list(map(int,r))for r in doc['A']],list(map(int,doc['b']))
def mod(A,b,d):
 return [[x%d for x in r]for r in A],[x%d for x in b]
A,b=coeff(json.loads((base/'tableau.json').read_text()))
q=17
for k in range(2,6):
 data=json.loads((D/'literals'/('mod17pow'+str(k)+'.json')).read_text())
 assert data['modulus']==17**k and data['exponent']==k
 a,c=coeff(data)
 assert mod(a,c,q)==(A,b)
 A,b,q=a,c,data['modulus']
 _,n,e=replay(A,b,q)
 assert e==data['bush_failure'] and e%17==2
 print('17^'+str(k),'lower-power compatible',n,'exact rooted checks; bush unit defect',e)

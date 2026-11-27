import sys
import pressure as f
from itertools import combinations
from math import prod
p=227
c,b,A=f.read(p,177,190,149)
B,c,b,H,eta=f.high(A,c,b)
u=[0,1]+f.solve([a[2:]for a in H],[-a[1]%p for a in H])
d1=H[4]
row=[z*x*x%p for z,x in zip(d1,c)]
v=f.rowmul(row,B)
mult=f.dot(row,u)
L=[(f.dot(v,[x**k%p for x in c]),mult*c[0]**k%p)for k in [1,2,3,4]]
print('canonical Lambda constants,slopes:',L)
assert f.det([list(x)for x in L[:2]])==3
print('det Lambda X/X² =',3)
R=H[:-1]
v=[0,0,1]+f.solve([a[3:]for a in R],[-a[2]%p for a in R])
print('relaxed basis v:',v, 'd1C² v=',f.dot(row,v))
print('relaxed high-only constraints column ranks:',
      [f.rank([a[j+1:]for a in R])[0] for j in range(8)])
m=[[(f.dot(f.rowmul(row,B),[x**k%p for x in c])),
     c[0]**k%p,c[1]**k%p]for k in [1,2,4]]
assert f.det(m)==178
assert f.det([a[3:]for a in R])
assert f.det([a[2:]for a in H])==159
print('relaxed 3-vector high gate',m,'det=',178)

if '--lean-source' in sys.argv:
    for k,M in {
      'canonicalColumns': [a[2:]for a in H],
      'relaxedColumns': [a[3:]for a in R],
      'canonicalMoment': [list(x)for x in L[:2]],
      'relaxedMoment': m,
    }.items():
      print('DEF',k,'MATRIX',M,'VALUE',f.det(M))

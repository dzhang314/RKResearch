import pressure as f
from itertools import permutations,combinations
import sys
from pathlib import Path
if len(sys.argv)<2:
 sys.argv.append(str(Path(__file__).parent.parent/'erk10-stepanov-five-opening'/'stepanov15-source.txt'))
p=227
c,_,_=f.read(p,177,190,149)
nodes=[c[i]for i in (8,10,6,7)]
assert nodes==[51,24,204,177]
def mul(F,a):
 g=[0]*(len(F)+1)
 for i,v in enumerate(F):g[i]=(g[i]-a*v)%p;g[i+1]=(g[i+1]+v)%p
 return g
def integral(F,r):return sum(a*r**(j+1)*f.inv(j+1) for j,a in enumerate(F))%p
def ev(r):return [r**d%p for d in range(1,5)]
def J(r):return [r**(d+1)*f.inv(d+1)%p for d in range(1,5)]
four=[]
for x,y,z in permutations(nodes,3):
 d=f.det([J(x),ev(x),ev(y),J(z)])
 four.append((x,y,z,d))
print('4-way predecessor determinants:',len(four),sum(bool(t[-1]) for t in four))
for t in four:
 if not t[-1]:print('ZERO4',t)
upper=[]
for a in nodes:
 for k in range(3):
    for S in combinations([v for v in nodes if v!=a],k):
      F=[-1,1]
      for b in S:F=mul(F,b)
      d=(integral(F,1)-integral(F,a))%p
      upper.append((a,S,d))
print('upper supports incl endpoint, at most 3 nodes:',len(upper),sum(bool(t[-1])for t in upper))
for t in upper:
 if not t[-1]:print('ZEROUP',t)

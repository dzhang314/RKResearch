from fractions import Fraction
from math import prod, lcm, factorial, gcd
import json
from pathlib import Path
t=json.load(Path(__file__).with_name("tableau20.json").open()); A=[list(map(Fraction,a)) for a in t['A']]; b=list(map(Fraction,t['b']))
s=len(b); assert s==20==len(A) and all(len(row)==20 and not any(row[i+1:]) for i,row in enumerate(A))
assert A[0][0]!=A[1][1]
a=lcm(*(z.denominator for row in A for z in row)); d=lcm(*(z.denominator for z in b)); D=lcm(a,d)
A=[[(j,int(a*z)) for j,z in enumerate(row) if z] for row in A]; B=[int(d*z) for z in b]
def mv(v): return tuple(sum(k*v[j] for j,k in row) for row in A)
def read(v): return sum(y*x for y,x in zip(B,v))
# Sorted tuples of child indices; extend by the last (largest) child.
size=[]; mult=[]; av=[]; forests=[{()}]
for n in range(1,13):
 if n>1:
  fs=set()
  for k in range(1,n):
   for head in forests[n-1-k]:
    for i,q in enumerate(size):
     if q==k and (not head or head[-1]<=i):fs.add(head+(i,))
  forests.append(fs)
 for kids in sorted(forests[n-1]):
  v=tuple(prod(av[i][j] for i in kids) for j in range(s))
  gamma=n*prod(mult[i] for i in kids)
  assert read(v)*gamma == d*a**(n-1),(n,kids)
  size.append(n); mult.append(gamma); av.append(mv(v))
counts=[size.count(i) for i in range(1,13)]
assert counts == [1,1,2,4,9,20,48,115,286,719,1842,4766]
u=(1,)*s
for _ in range(12):u=mv(u)
scale=d*a**12
tall=Fraction(factorial(13)*read(u),scale)-1
bush=Fraction(13*read([x**12 for x in av[0]]),scale)-1
assert gcd(tall.numerator,bush.numerator)==1 and D**13%lcm(tall.denominator,bush.denominator)==0
assert (str(tall),str(bush))==(t['scaled_next_tall'],t['scaled_next_bush'])
print('Trees:',sum(counts),'denominator bits:',D.bit_length(),'bush:',bush,'two numerator gcd:',gcd(tall.numerator,bush.numerator))

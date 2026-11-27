"""Exact good-reduction exclusion of a reverse literal Gauss triple."""
from flint import nmod_poly
from itertools import permutations
from sympy import isprime

def check():
 p=1129
 assert isprime(p)
 L=nmod_poly([1,-20,90,-140,70],p)
 roots=[int(x) for x,m in L.roots() if m==1]
 assert sorted(roots)==[100,214,916,1030]
 for g,y in permutations(roots,2):
  assert L((2*y-g)%p)!=0
  assert L((4*g-y)%p)!=0
 print("Both literal reverse triple incidences fail at all ordered Gauss pairs.")
if __name__=='__main__':check()

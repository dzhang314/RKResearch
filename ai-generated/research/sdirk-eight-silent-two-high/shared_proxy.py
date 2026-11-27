"""Finite diagonal for eight active, one repeated Gauss clock, T nonzero."""
from equal_detected import ends
from variable_gamma import *
from unequal_finite import Lco

def transfer(front):
 A,B,r=ends(front,1)
 h_a,h_b=(A-1)/2,(B-1-r)/2
 Q0=G*(B*h_b*Lf(G*A)-A*h_a*Lf(G*B))
 Q1=h_a*Lf(G*B)-h_b*Lf(G*A)
 S=sum(K.convert(v)*(-Q0)**j*Q1**(4-j) for j,v in enumerate(Lco))
 D=G*(2*G-1)*Q1
 assert S
 while True:
  F=S.gcd(D)
  if F.degree()==0:break
  S=S.exquo(F)
 S=S.exquo(S.gcd(S.diff(G))).monic()
 ans=[(m.degree(),e) for m,e in S.factor_list()[1]]
 assert sorted(ans)==[(4,1),(4,1),(12,1)]
 print('eight on seven clocks: guarded diagonal factor degrees',front,ans,flush=True)
 return S
if __name__=='__main__':
 for f in (True,False):transfer(f)

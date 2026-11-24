"""Independent integer replay of the two fixed 3 x 3 moment determinants."""
from itertools import combinations
cases=((9,10709,[0,1103,3759,4862,5525,7562,7742,7829,8009,10046],840,9031),
       (10,15727,[0,1069,1186,6796,7356,7876,8398,8920,9440,10000,15610],1320,4723))
for m,p,S,n0,prod0 in cases:
 n,prod=0,1
 for a,b,c in combinations(S,3):
  for u in S:
   if u in (a,b,c):continue
   h=[-a*b*c*(2520//(k+1))+(a*b+a*c+b*c)*u*(2520//(k+2))-(a+b+c)*u**2*(2520//(k+3))+u**3*(2520//(k+4)) for k in range(1,6)]
   x,y,z,v,w=h
   det=(x*z*w-x*v*v-y*y*w+2*y*z*v-z**3)%p
   assert det
   prod=prod*det%p;n+=1
 print(m,p,n,prod)
 # Scaling the four roots multiplies a determinant by t^9.
 scale={9:4862,10:16796}[m]
 assert (n,prod)==(n0,prod0)
 print("unscaled product",prod*pow(pow(scale,9*n,p),-1,p)%p)

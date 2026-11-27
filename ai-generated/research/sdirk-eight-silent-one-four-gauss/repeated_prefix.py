"""Four Gaussian active rows, repeated last silent prefix clock."""
from distinct_prefix import *

def repeated(p,g,A,B,mid,ha,hb,H4,r0):
 I=lambda v:pow(int(v)%p,-1,p)
 r=r0*I(g)%p
 P=lambda c:nmod_poly(c,p)
 def L(j):return (r**(j+1)*I(j+1)-r**j)%p
 def LR(F):return sum(int(F[j])*L(j) for j in range(F.degree()+1))%p
 Q=P([-A,1])*P([-B,1])
 z=LR(Q*P([0,1]))*I(LR(Q))%p
 assert z!=A and z!=B
 zh=int(H4(z));z1=2*zh%p
 za=(B*(z-1-z1)-(z*z*I(2)-z-z1))*I(B-A)%p
 zb=(z-1-z1-za)%p
 ns=[A,B,z];hs=[ha,hb,zh]
 # Derivative wrt actual h at fixed current clock.
 D0=[-2,-2,-4*I(3)]
 taps=[]
 for j,q in enumerate(ns):
  a,b=[v for i,v in enumerate(ns) if i!=j]
  n=((a*b)*D0[0]-(a+b)*D0[1]+D0[2])*I((q-a)*(q-b))%p
  taps.append(n)
 dAh=(1+sum(t*h for t,h in zip(taps,hs)))%p
 dTau=(2+sum(t*n**3 for t,n in zip(taps,ns)))%p
 T=lambda y,w,v:(y**3-y**4*I(4)+sum(h*n**3 for h,n in zip(w,v)))%p
 head=[
   [ha,A*ha,ha,T(A,[A-1],[1]),L4(p,g*A)],
   [hb,B*hb,hb+mid*ha,T(B,[B-1-mid,mid],[1,A]),L4(p,g*B)],
   [zh,z*zh,zh+za*ha+zb*hb,T(z,[z1,za,zb],[1,A,B]),L4(p,g*z)]
 ]
 def det(H):
  return sum((-1)**sum(pi[i]>pi[j] for i in range(4) for j in range(i+1,4))*
             product_i(H[i][pi[i]] for i in range(4)) for pi in permutations(range(4)))%p
 for y in ns:
  T0=head+[[1,y,dAh,dTau,0]]
  assert any(det([[q[i] for i in ix] for q in T0]) for ix in combinations(range(5),4))
 return True
def verify(p,t):
 for root,st,g,a,b,tap,ha,hb,h4p in configs(p,t):
  for r in root:
   assert repeated(p,g,a,b,tap,ha,hb,h4p,r)
 return True
if __name__=='__main__':print('repeated checks',verify(1129,203))

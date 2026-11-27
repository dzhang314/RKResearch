"""Five distinct ordinary and reverse k=0 with active eighth."""
from early_repeated import *
from off8_fibers import det
from equal_undetected_front import lagrange
from early_fourth import check as early_fourth

def derivative_test(front,rear,sg,M,H,p,t):
 A0,B0,_=ends(front,1)
 # A row-four clock at x cannot also be a literal front clock.
 M=M.exquo(M.gcd((G*(1+A0)-1)*(G*(1+B0)-1)))
 if M.degree()==0:return True
 for U,g,x,Y,h0,A,B,mid,ha,hb in reduced(front,rear,sg,M,H,p,t):
  z=x/g
  h=ev(h0,z)
  ta=(B*(z-1-2*h)-(z*z/2-z-2*h))/(B-A)
  tb=z-1-2*h-ta
  nodes=[A,B,z]
  d3=lagrange(nodes)
  v0=[U(-2),U(-2),-U(4)/3]
  td=[sum(x*y for x,y in zip(r,v0)) for r in d3]
  dh=1+sum(x*y for x,y in zip(td,[ha,hb,h]))
  dt=2+sum(t*d**3 for t,d in zip(td,nodes))
  def tau(x,w,node):return x**3-x**4/4+sum(i*j**3 for i,j in zip(w,node))
  root=[U(i) for i in Lco]
  p0=lambda r:ev(root,g*r)
  R=[
   [ha,A*ha,ha,tau(A,[A-1],[U(1)]),p0(A)],
   [hb,B*hb,hb+mid*ha,tau(B,[B-1-mid,mid],[U(1),A]),p0(B)],
   [h,z*h,h+ta*ha+tb*hb,tau(z,[2*h,ta,tb],[U(1),A,B]),p0(z)],
   [U(1),z,dh,dt,U(0)]]
  M0=[det([[r[i] for i in I] for r in R]) for I in combinations(range(5),4)]
  # Over the finite field for this irreducible component, one nonzero minor suffices.
  assert any(M0)
 return True

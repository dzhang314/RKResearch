"""Detected-seven ordinary triple, k=0 and active physical eighth."""
from early_repeated import *
from early_fourth import test_first
from off8_fibers import det
from equal_undetected_front import lagrange

def verify(front,rear,sg,M,H,p,t):
 for U,g,x,Y,h0,A,B,mid,ha,hb in reduced(front,rear,sg,M,H,p,t):
  cv=lambda q:U(Epoly(JJ(q))) if q else U(0)
  Rp=ends(rear,sg)[0]
  c9=1-g*cv(Rp)
  ev(h0,c9/g).inv()
  # Additional virtual h=0 row five at the physical penultimate peg.
  test_first(U,g,A,B,mid,ha,hb,h0,c9/g)

 for zslot in (9,10):
  A0,B0,_=ends(front,1)
  R0=ends(rear,sg)[0] if zslot==9 else K.one
  M0=M.exquo(M.gcd((G*(A0+R0)-1)*(G*(B0+R0)-1)))
  if M0.degree()==0:continue
  for U,g,x,Y,h0,A,B,mid,ha,hb in reduced(front,rear,sg,M0,H,p,t):
   cv=lambda q:U(Epoly(JJ(q)))
   z=1/g-cv(R0);h=ev(h0,z)
   ta=(B*(z-1-2*h)-(z*z/2-z-2*h))/(B-A)
   tb=z-1-2*h-ta
   ns=[A,B,z];LG=lagrange(ns)
   q0=[U(-2),U(-2),-U(4)/3]
   dt=[sum(a*b for a,b in zip(n,q0)) for n in LG]
   dAh=1+sum(v*h0 for v,h0 in zip(dt,[ha,hb,h]))
   dT4=2+sum(v*c**3 for v,c in zip(dt,ns))
   def tau(x,w,node):return x**3-x**4/4+sum(i*j**3 for i,j in zip(w,node))
   p0=lambda a:sum(U(j)*(g*a)**i for i,j in enumerate(Lco))
   R=[
    [ha,A*ha,ha,tau(A,[A-1],[U(1)]),p0(A)],
    [hb,B*hb,hb+mid*ha,tau(B,[B-1-mid,mid],[U(1),A]),p0(B)],
    [h,z*h,h+ta*ha+tb*hb,tau(z,[2*h,ta,tb],[U(1),A,B]),p0(z)],
    [U(1),z,dAh,dT4,U(0)]]
   assert any(det([[r[i] for i in I] for r in R]) for I in combinations(range(5),4))
 return True

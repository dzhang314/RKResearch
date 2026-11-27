"""Gauss-double chart, nonmidpoint: actual two- or three-coordinate reverse block."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high"):
 sys.path.insert(0,str(root/dep))
from shared_proxy import transfer
from equal_detected import ends
from unequal_finite import *
from variable_gamma import Lf

def reduced(star,H,p,t):
 B0=Bfield(nmod_poly([0,1],p),p,t);M=B0.cast(Epoly(H))
 assert M.degree()==H.degree() and M.leading_coefficient()==1
 for f,e in M.factor()[1]:
  assert e==1
  B=Bfield(f,p,t)
  g=B(nmod_poly([0,1],p));x=1-g
  A,C,hm=ends(star,1)
  cast=lambda c:B(Epoly(JJ(c))) if c else B(0)
  a,b,ha,hb=map(cast,(A,C,(A-1)/2,(C-1-hm)/2))
  a,b=a*g,b*g
  L=list(map(B,Lco))
  d=(ev(L,b)/hb-ev(L,a)/ha)/(b-a)
  r=a-(ev(L,a)/ha)/d
  P,rem=qr(L,[-r,B(1)]);assert not rem and len(P)==4
  for v in [g,x-g,x-r,g-r,ev(L,g),ev(L,x)]:
   v.inv()
  yield B,g,x,r,P,a,b

def powers(p,n):
 r=[p[0].A(1)]
 for _ in range(n):r=mul(r,p)
 return r

def checks(B,g,x,r,P,a,b):
 u=[B(0),B(1)];k=[B(1),B(2),B(-1)]
 Dx=ev(P,x)
 c=[x,-g]
 subst=lambda s:sum_poly([sc(powers(s,j),v) for j,v in enumerate(P)])
 D=lambda node: add(node,[-g])
 F9=add(sc(subst(c),x-g),sc(mul(k,D(c)),-Dx))
 assert len(F9)==4 and F9[0]==0
 Si=add([2*(g-x)],sc(mul(k,[B(-2),B(1)]),-g))
 assert ev(Si,(x-r)/g)
 # Silent eighth, active ninth singleton.
 E=gcdp(F9,Si)
 assert len(E)==1
 for star in (True,False):
  V=[B(2),B(-1)] if star else [B(0),B(2)]
  d=add([x],sc(V,-g))
  if star:den=[B(1)];q3=k
  else:
   den=[B(-2),B(1),B(4),B(-1)]
   q3=add(mul([B(1),B(4),B(-4)],den),[B(0),B(0),B(-8),B(12)])
  F8=add(sc(mul(subst(d),den),x-g),sc(mul(q3,D(d)),-Dx))
  # The other tail singleton in each of the two repeat positions.
  c_r=(x-r)/g
  d_r=2-c_r if star else c_r/2
  ev(F8,c_r).inv()
  ev(F9,d_r).inv()
  assert F9[0]==0
  E=gcdp(F9[1:],F8)
  assert len(E)==1
 return True

def main():
 p,t=1009,285
 assert SY.isprime(p) and (2*t*t-1)%p==0
 for s in (True,False):
  for H,e in transfer(s).factor_list()[1]:
   assert e==1
   H=H.monic()
   A,C,R=ends(s,1);ha,hb=(A-1)/2,(C-1-R)/2
   Q0=G*(C*hb*Lf(G*A)-A*ha*Lf(G*C));Q1=ha*Lf(G*C)-hb*Lf(G*A)
   assert H.gcd((Q0+Q1*(1-G))*(Q0+Q1*G)*Lf(G)).degree()==0
   checks_at_prime=[checks(*D) for D in reduced(s,H,p,t)]
   assert all(checks_at_prime)
   print('all literal active/silent and double/singleton tail orientations excluded',
         'front phase',s,'degree',H.degree(),'components',len(checks_at_prime))
if __name__=='__main__':main()

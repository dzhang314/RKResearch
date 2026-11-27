"""Five ordinary sites with early silent fourth, terminal double."""
from early_repeated import *
from off8_fibers import multicol
from flint import fq_default_ctx,fq_default_poly_ctx,fmpz_mod_poly_ctx

def split(B,E):
 F=fq_default_ctx(modulus=fmpz_mod_poly_ctx(B.p)([int(x) for x in B.M]),fq_type='FQ_NMOD')
 P0=fq_default_poly_ctx(F)
 p=P0([F([int(q) for q in v.x]) for v in E])
 assert p.degree()==len(E)-1
 for m,e in p.factor()[1]:
  cf=[B(nmod_poly([int(t) for t in z.polynomial()],B.p)) for z in m]
  assert cf[-1]==1
  yield cf
def test_first(V,g,A,B,r,ha,hb,h0,y):
 K=V(1)
 z=[V(0),K]
 L=[V(v)*g**j for j,v in enumerate(Lco)]
 Ia,Ib=K/(B-A),K/(A-B)
 ta=sc(add([B*(0-1),B+1,-K/2],sc(h0,2*(1-B))),Ia)
 tb=add(add([-1,K],sc(h0,-2)),sc(ta,-1))
 hz=h0
 Az=add(hz,add(sc(ta,ha),sc(tb,hb)))
 Tz=add([V(0),V(0),V(0),K,-K/4],sum_poly([sc(hz,2),sc(ta,A**3),sc(tb,B**3)]))
 aa,ab=ha,hb+r*ha
 tA=A**3+(A-1)-A**4/4
 tB=B**3+(B-1-r)+r*A**3-B**4/4
 def affine(v,w):
  S=(w/hb-v/ha)/(B-A)
  return [v/ha-A*S,S]
 U=add(L,sc(mul(affine(ev(L,A),ev(L,B)),hz),-1))
 X=add(Tz,sc(mul(affine(tA,tB),hz),-1))
 Y=add(Az,sc(mul(affine(aa,ab),hz),-1))
 M0,M1,M2=y-1,y**2/2-y,y**3/3-y*y
 B0=add([M2-B*M1],sc(z,B*M0-M1))
 A0=add([M2-A*M1],sc(z,A*M0-M1))
 WA=sc(mul([-B,K],B0),-Ib)
 WB=sc(mul([-A,K],A0),-Ia)
 WC=M2-(A+B)*M1+A*B*M0
 J=nodal([A,B])
 TF=sum_poly([sc(J,y**3-y**4/4),sc(WA,A**3),sc(WB,B**3),[V(0),V(0),V(0),WC]])
 AF=sum_poly([sc(WA,ha),sc(WB,hb),sc(hz,WC)])
 f=add(sc(mul(J,X),ev(L,y)),sc(mul(TF,U),-1))
 h=add(sc(mul(J,Y),ev(L,y)),sc(mul(AF,U),-1))
 div_J=lambda f: qr(f,J)
 for p0 in (U,X,Y,TF,AF):
  q0,r0=div_J(p0);assert not r0
 F,R=qr(f,mul(J,J));G,S=qr(h,mul(J,J));assert not R and not S
 assert len(F)==4 and G
 Z=gcdp(F,G)
 assert len(Z)==1
 return len(F)-1,len(G)-1

def check(front,rear,e,M,H,p,t):
 for U,g,x,Q,h0,A,B,r,ha,hb in reduced(front,rear,e,M,H,p,t):
  test_first(U,g,A,B,r,ha,hb,h0,x/g)
  for p0 in split(U,Q):
   V=Tower(p0);y=V.gen()
   test_first(V,*map(V,(g,A,B,r,ha,hb)),list(map(V,h0)),y)
 return True

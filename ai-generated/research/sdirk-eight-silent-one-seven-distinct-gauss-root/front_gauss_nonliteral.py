"""Pure-four chronology after Gauss-hole tail projection."""
from gauss_tail_nonliteral import *

def fterms(F,fd,a,s,H4):
 h4=ev(list(map(F,H4)),s)
 A0,B0=map(F,fd[:2])
 L0,e=list(map(F,fd[9])),list(map(F,fd[10]))
 tau,ah=map(F,fd[11:13])
 XT=ev(list(map(F,exact_uc_y(fd[14]))),s)
 XA=ev(list(map(F,exact_uc_y(fd[15]))),s)
 dT=ev(list(map(F,fd[16])),s)
 dA=ev(list(map(F,fd[17])),s)
 ab=A0*B0;ss=A0+B0
 m0=[F(-1),F(1)]
 m1=[F(0),F(-1),F(1)/2]
 m2=[F(0),F(0),F(-1),F(1)/3]
 J=sum_poly([m2,sc(m1,-ss),sc(m0,ab)])
 T0=sum_poly([[F(0)]*3+[F(1),F(-1)/4],sc(m2,ss),sc(m1,-ab),sc(J,s)])
 A0=sum_poly([sc(m0,L0[0]),sc(m1,L0[1]),sc(J,ev(e,s))])
 T1=[h4*(dT-tau)+XT*a,-XT]
 A1=[h4*(dA-ah)+XA*a,-XA]
 return h4,T0,A0,T1,A1

def test5(F,gg,r,a,s,H4,fd,Q,P,which,hit):
 h,T0,A0,T1,A1=fterms(F,fd,a,s,H4)
 yR=r/gg
 if which==5:
  # The silent fifth has its own unknown defect; eliminate between the two
  # exact affine reads. H4!=0 because the fourth is genuinely ordinary.
  Dt=ev(T0,yR)*ev(A1,yR)-ev(A0,yR)*ev(T1,yR)
  Dt.inv()
  return True
 RT=add(sc(T0,h*Q),mul(T1,P));RA=add(sc(A0,h*Q),mul(A1,P))
 RT,ET=qr(RT,[-a,F(1)]);RA,EA=qr(RA,[-a,F(1)]);assert not ET and not EA
 n=3
 if which!=4:
  RT,ET=qr(RT,[-s,F(1)]);RA,EA=qr(RA,[-s,F(1)]);assert not ET and not EA
  n=2
 rv=polyres(F,RT,RA,n,n)
 rv.inv()
 # When the hole is already in the actual tail, fifth cannot be that hole.
 if not hit:span_unit(F,ev(T0,yR),ev(A0,yR))
 return True

def phase(f,i,mode,hit,p,t):
 fd=frontdata(f,i);n=0
 # A genuinely active fourth cannot be the Gauss hole: H4=0 would
 # force Ah4=0. This exact literal gcd does not use a good prime.
 assert len(gcdp(fd[8],exact_uc_y(fd[19])))==1
 for U,g,u,r in fields(mode,hit,p,t):
  n+=1
  g.inv()
  a,b,hh=map(U,fd[5:8])
  h4=list(map(U,fd[8]))
  Qp=Pcoeff(U,r)
  I=[g**j*v for j,v in enumerate(Qp)]
  Q=ev(I,a);P=sc(I,hh)
  if mode is not None:
   assert test5(U,g,r,a,r/g,h4,fd,Q,P,4,hit)
  Phi,e=qr(add(sc(h4,Q),sc(P,-1)),[-a,U(1)])
  assert not e and len(Phi)==3
  Phi[-1].inv()
  W=Nested(mon(Phi));s=W.gen()
  for k in ((5,6) if mode is not None else (6,)):
   assert test5(W,W(g),W(r),W(a),s,list(map(W,h4)),fd,W(Q),list(map(W,P)),k,hit)
 assert n
 print('verified Gauss reverse root:',f,i,mode,hit,p,n,flush=True)
 return True

"""Denominator-free marked-sixth cut when row six may be the Gauss copy."""
from one_front_zero import *
from both_front_silent8 import context

def scaled_six(F,g,r,A,B,m,anc,ha0,s,y,pegs,H4,ht):
 X=1/g-1;R=r/g
 ha,hb=(A-1)/2,(B-1-m)/2
 h4s=ev(H4,s)
 tr=A**3+A-1-A**4/4 if anc==A else B**3+B-1-m+m*A**3-B**4/4
 ar=ha if anc==A else hb+m*ha
 qa,qt=ar/ha0,tr/ha0
 ta=(B*(s-1-2*h4s)-(s*s/2-s-2*h4s))/(B-A)
 tb=s-1-2*h4s-ta
 t4=s**3-s**4/4+2*h4s+ta*A**3+tb*B**3
 a4=h4s+ta*ha+tb*hb
 dt0=t4-qt*h4s;da0=a4-qa*h4s
 dl=h4s*(s-anc)
 QT=[qt*dl-dt0*anc,dt0];QA=[qa*dl-da0*anc,da0]
 Lh,AA,e,_,_=context(F,A,B,m,ha,hb,None,H4)
 H2=add(Lh,sc(nodal([A,B]),ev(e,s)))
 F3=nodal([A,B,s])
 PP=[w*g**j for j,w in enumerate(Pcoeff(F,r))]
 D0=ev(PP,anc);Pnum=sc(PP,ha0)
 h5num=ev(Pnum,y)
 base=[[-F(1),F(1)],[F(0),-F(1),F(1)/2],
       [F(0),F(0),-F(1),F(1)/3],
       [F(0),F(0),F(0),-F(1),F(1)/4]]
 def suff(H):
  b=[add(sc(v,D0*dl),sc(H,c*dl)) for v,c in zip(base[:3],(-2,-2,-F(4)/3))]
  b.append(add(sc(base[3],D0*dl),mul(H,add(QT,[-2*dl]))))
  L=add(mul(H,add(QA,[-dl])),sc(sum_poly([sc(v,c) for v,c in zip(b,H2)]),-1))
  T=sum_poly([sc(v,c) for v,c in zip(b,F3)])
  return add(sc(L,D0*ev(F3,y)),sc(T,D0*ev(H2,y)-h5num))
 Mask=nodal(pegs);m0,m1=[intp(F,Mask,j) for j in range(2)]
 Q=suff(Pnum)
 E=sum(q*m1**j*(m0*g)**(len(Q)-1-j) for j,q in enumerate(Q))
 # Alternative: row six is the second physical r, with unknown actual cubic amplitude.
 Bnod,rem=qr(Mask,[-r,F(1)]);assert not rem
 V=mul(Bnod,[-m1,m0])
 DR=ev(V,r);IR=intp(F,V)
 v=DR*intp(F,Pcoeff(F,r))/Pphys(F,r,r)
 p=ev(Pnum,R);hn=ha0*ht
 def mass(h):return IR*(p-D0*h)*(p-hn)-v*p*(p-D0*h-hn)
 G0,G1=ev(suff([F(0)]),R),ev(suff([D0]),R)
 M0,M1=mass(F(0)),mass(F(1))
 Z=M0*(G1-G0)-(M1-M0)*G0
 return E,Z

"""Both actual silent zero rows share the reverse-root literal front clock."""
from common_rear import *
from no_front_nonzero import data
from one_front_zero import do5,sites,slopes,row5,two_pivots,conditional_zero

def front_shared(F,r,g,u,front,zslot,rear,hit,silent):
 A,B,m,Z=phase(F,front,zslot)
 anc=A if zslot==1 else B
 ha,hb=(A-1)/2,(B-1-m)/2
 x,c=1-g,1-g*(1+u)
 d=1-g*(3-u if rear else 1+2*u)
 X,C,D,R=x/g,c/g,d/g,r/g
 p=Pcoeff(F,r)
 S=[w*g**j for j,w in enumerate(p)]
 S=sc(S,(ha if zslot==1 else hb)/ev(S,anc))
 H4=[F(Epoly(JJ(v))) for v in pol(h4(front),lambda v:v)]
 pegs=[anc,X,C]+([] if silent else [D])+([] if hit else [R])
 (1+2*u-u*u).inv();u.inv()
 (anc-R).inv()
 (g*Z-r).inv()
 if silent:assert 2*(Z-X)==(1+2*u-u*u)*(u-2)
 else:
  for v in pguards(F,r,g,x,g*Z,c,d,hit):
   v.inv()
 for i,tt in ((10,X),(9,C))+(() if silent else ((8,D),)):
  if i==hit:assert tt==R
  else:
   (tt-R).inv()
   ev(S,tt).inv()
  (tt-Z).inv()
  (tt-anc).inv()
 (X-C).inv()
 if not silent:(D-C).inv();(D-X).inv()
 if len(pegs)>=4:
  Y=sites(F,g,pegs)
  if not Y:return
  # Row four is always active; it cannot repeat the literal silent root.
  do5(F,g,Z,R,A,B,m,anc,ha,hb,S,H4,pegs,R,ev(H4,R),Y,0 if hit else 1,not silent)
  W=Nested(Y);s=W.gen()
  hh=ev(list(map(W,H4)),s)
  cc=list(map(W,(g,Z,R,A,B,m,anc,ha,hb)))
  SW,HW=[list(map(W,v)) for v in (S,H4)]
  if conditional_zero(W,hh-ev(SW,s)):return
  YY,er=qr(list(map(W,Y)),[-s,W(1)]);assert not er
  do5(W,*cc,SW,HW,list(map(W,pegs)),s,hh,YY if len(YY)>1 else [],2,not silent)
  return
 assert silent and hit and len(pegs)==3
 # Row four can be the other physical r-copy, so row five is an unpegged singleton.
 h=ev(H4,R)
 tr=A**3+A-1-A**4/4 if anc==A else B**3+B-1-m+m*A**3-B**4/4
 ar=ha if anc==A else hb+m*ha
 QT,QA=slopes(A,B,m,ha,hb,R,h,ar,tr,anc)
 T,U=row5(F,A,B,R,ha,hb,h,QT,QA,S)
 T,re=qr(T,[-anc,F(1)]);assert not re and len(T)==4
 U,re=qr(U,[-anc,F(1)]);assert not re and len(U)==4
 multicol(mon(T),U).inv()
 # Any singleton row four supplies the missing fourth peg.
 G,rem=qr(add(H4,sc(S,-1)),[-anc,F(1)]);assert not rem and len(G)==3
 W=Nested(mon(G));s=W.gen()
 h=ev(list(map(W,H4)),s)
 cc=list(map(W,(g,Z,R,A,B,m,anc,ha,hb)))
 SW,HW=[list(map(W,v)) for v in (S,H4)]
 pegs=list(map(W,pegs))+[s]
 do5(W,*cc,SW,HW,pegs,s,h,two_pivots(W,W(g),pegs),2,False)

def check(front,zslot,rear,hit,silent,p,t):
 for F,r,g,u in (silent_z_pts(front,zslot,hit,p,t) if silent else star_constant(front,zslot,rear,hit,p,t)):
  front_shared(F,r,g,u,front,zslot,rear,hit,silent)
 return True

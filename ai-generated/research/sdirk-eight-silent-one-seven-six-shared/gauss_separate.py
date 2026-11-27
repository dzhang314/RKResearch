"""Active literal front at r, sole separate silent reverse-root stage."""
from gauss_front_pair import *
from one_front_zero import test_nonzero,conditional_zero
from no_front_nonzero import mod_base
from both_front_active8 import tail_poly
from arithmetic_nonzero import guarded,pseudo
from both_front_silent8 import nextgate,context as literal_context
from one_front_zero import slopes

@lru_cache(None)
def tails(front,slot,rear,hit,silent):
 F=B0
 cv=lambda x:F(Epoly(JJ(x))) if x else F(0)
 A,B,m=map(cv,ends(front,1));R,off=(A,B) if slot==0 else (B,A)
 g=R0/R;X=1/g-1
 pp=[q*g**j for j,q in enumerate(PX)]
 u,k,c,d,H,q3,A9,B9,A8,B8=tail_poly(F,X,R,pp,rear)
 if silent:
  dd=add([X],sc(mul(k,[F(-2),F(1)]),F(1)/2))
  zs,dr=dd,[F(1)]
 else:
  zs,dr=(B8,A8) if hit==9 else (B9,A9)
 if hit:
  v=X-R
  if hit==8:v=2-v if rear else v/2
  G=[-v,F(1)]
 elif silent:G=add(B9,sc(mul(A9,zs),-1))
 else:G=add(mul(A9,B8),sc(mul(A8,B9),-1))
 D1=[u,k,add(zs,sc(dr,-off)),add(zs,sc(dr,-R)),add(zs,sc(dr,-X)),dr]
 if hit!=9:D1.extend((add(c,[-R]),subst(pp,c)))
 if not silent and hit!=8:D1.extend((add(d,[-R]),subst(pp,d)))
 if not silent:D1.extend((add(d,sc(c,-1)),add(d,[-X]),H))
 D1.extend([add(zs,sc(mul(dr,c),-1))])
 if not silent:D1.append(add(zs,sc(mul(dr,d),-1)))
 assert G
 if not all(D1):G=[F(1)]
 else:G=mon(guarded(G,D1))
 print('active Gauss front fixed diagonal tail',front,slot,rear,hit,silent,len(G)-1,flush=True)
 return G,g,X,R,A,B,m,pp,zs,dr

def context_tail(front,slot,rear,hit,silent,p,t):
 G,g,X,R,A,B,m,pp,zs,dr=tails(front,slot,rear,hit,silent)
 if len(G)<=1:return
 F,rr=mod_base(p,t)
 U=Tower(list(map(F,G)));u=U.gen();r=U(rr)
 g,X,R,A,B,m=map(U,(g,X,R,A,B,m));pp=list(map(U,pp))
 Z=ev(list(map(U,zs)),u)/ev(list(map(U,dr)),u)
 C=X-u;D=X-(2-u if rear else 2*u)
 k=1+2*u-u*u;H=U(1) if rear else -2+u+4*u*u-u**3
 Q3=k if rear else -k*(4*u**3-12*u*u+3*u+2)
 ha,hb=(A-1)/2,(B-1-m)/2
 k.inv();u.inv();(X-R).inv()
 (Z-A).inv();(Z-B).inv();(X-Z).inv();(C-Z).inv()
 if not silent:(D-Z).inv();H.inv()
 (C-X).inv()
 if hit==9:assert C==R
 else:(C-R).inv();ev(pp,C).inv()
 if not silent:
  if hit==8:assert D==R
  else:(D-R).inv();ev(pp,D).inv()
  (D-X).inv();(D-C).inv()
 vn=ev(pp,X)
 hp=ha if slot==0 else hb
 rrh=U(0) if not hit else vn*(k*(C-Z) if hit==9 else Q3*(D-Z)/H)/(X-Z)
 pegs=[R,X]+([] if hit==9 else [C])+([] if silent or hit==8 else [D])
 yield U,r,g,X,R,A,B,m,pp,Z,hp,rrh,pegs

def span_unit(F,*values):
 for v in values:
  if conditional_zero(F,v):return True
 for j in range(1,12):
  v=sum(a*F(j)**i for i,a in enumerate(values))
  if conditional_zero(F,v):return True
 raise ArithmeticError('no visible residual combination is a unit')

def tail_mass(F,r,g,R,pp,headh,tailh,pegs,s,y,Pscale):
 pegs=list(pegs)+[s,y]
 assert 4<=len(pegs)<=6 and pegs[0]==R
 D=nodal([g*n for n in pegs]);V=nodal([g*n for n in pegs[1:]])
 m=[intp(F,D,j) for j in range(4 if len(pegs)==4 else (3 if len(pegs)==5 else 2))]
 if len(pegs)==4:
  a,b,c,d=m
  V=mul(V,[b*d-c*c,b*c-a*d,a*c-b*b])
 elif len(pegs)==5:
  a,b,c=m
  V=mul(V,[-b,a])
 defect=Pscale*ev(pp,R)
 nu= intp(F,Pcoeff(F,r))/Pphys(F,r,r)
 w0=intp(F,V);w1=ev(V,r)
 ee=w0*(defect-headh)*(defect-tailh)-w1*nu*defect*(defect-headh-tailh)
 return ee,m

def row6gate(F,g,R,A,B,m,S,pp,H4,s,y,ms):
 ha,hb=(A-1)/2,(B-1-m)/2
 h4s=ev(H4,s)
 tr=A**3+A-1-A**4/4 if R==A else B**3+B-1-m+m*A**3-B**4/4
 ar=ha if R==A else hb+m*ha
 QT,QA=slopes(A,B,m,ha,hb,s,h4s,ar,tr,R)
 Sold,AA,e,_,_=literal_context(F,A,B,m,ha,hb,None,H4)
 P=sc(pp,S)
 G=nextgate(F,A,B,Sold,e,TA=QT,QA=QA,C=P,Z=s,y=y,h=ev(P,y))
 a,b,c,d=ms
 Y=[b*d-c*c,(b*c-a*d)*g,(a*c-b*b)*g*g]
 if not Y[-1]:return F(0)
 L=G
 while len(L)>=3:
  L=add(sc(L,Y[-1]),[F(0)]*(len(L)-3)+sc(Y,-L[-1]))
 while len(L)<2:L.append(F(0))
 l,m=L
 return Y[2]*l*l-Y[1]*l*m+Y[0]*m*m

def direct_early(U,TF,AF,Z):
 # If the sole silent is row four (s=Z) or row five (y=Z), it is on the same actual profile.
 for earlier in (True,False):
  if earlier:E,G=substitute(U,TF,Z),substitute(U,AF,Z)
  else:
   E=sum_poly([sc(list(map(U,v)),Z**j) for j,v in enumerate(TF)])
   G=sum_poly([sc(list(map(U,v)),Z**j) for j,v in enumerate(AF)])
  assert len(E)==4 and len(G)==4
  multicol(mon(E),G).inv()
 return True

def late(U,r,g,X,R,A,B,m,pp,hp,hr,pegs,TF,AF,H4,hit,P,cut):
 W=Nested(list(map(U,P)));s=W.gen()
 T=substitute(W,TF,s);J=substitute(W,AF,s)
 assert len(T)==4 and len(J)==4
 if cut:
  T,re=qr(T,[-W(R),W(1)]);assert not re and len(T)==3
  J,re=qr(J,[-W(R),W(1)]);assert not re and len(J)==3
 F=Nested(mon(T));y=F.gen();s=F(s)
 r,g,X,R,A,B,m,hp,hr=map(lambda z:F(W(z)),(r,g,X,R,A,B,m,hp,hr))
 pp=list(map(lambda z:F(W(z)),pp));pegs=list(map(lambda z:F(W(z)),pegs))
 H4F=list(map(F,[W(c) for c in H4]))
 S=ev(H4F,s)/ev(pp,s)
 e=ev(list(map(F,J)),y)
 if hit:
  mass,ms=tail_mass(F,r,g,R,pp,hp,S*hr,pegs,s,y,S)
  other=([ms[0]*ms[2]-ms[1]**2] if len(pegs)==3 else [row6gate(F,g,R,A,B,m,S,pp,H4F,s,y,ms)])
  span_unit(F,e,mass,*other)
 else:
  D=nodal([g*n for n in pegs+[s,y]])
  if len(D)==7:span_unit(F,e,intp(F,D),intp(F,D,1))
  else:
   assert len(D)==6
   a,b,c=[intp(F,D,j) for j in range(3)]
   span_unit(F,e,a*c-b*b)

def verify(front,slot,rear,hit,silent,p,t):
 duplicate(front,slot)
 TF,AF,p0,H4=pair(front,slot)
 for U,r,g,X,R,A,B,m,pp,Z,hp,hr,pegs in context_tail(front,slot,rear,hit,silent,p,t):
  if not silent:
   ev(list(map(U,H4)),Z).inv();ev(pp,Z).inv()
   assert direct_early(U,TF,AF,Z)
  for P,cut in split_project(front,slot):
   late(U,r,g,X,R,A,B,m,pp,hp,hr,pegs,TF,AF,H4,hit,P,cut)
 return True

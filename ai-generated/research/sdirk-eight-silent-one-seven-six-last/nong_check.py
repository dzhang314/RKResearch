"""Remaining non-Gauss front / sole separate silent rank and chronology tests."""
from nong_tail import *
from nong_front import core,parts
from nong_parts import modparts
from gauss_separate import tail_mass
from nong_sparse import scaled_six

def cast_poly(P,W,g,cv):
 Q={}
 for (i,j,k),v in parts(P).items():
  key=(i,j)
  Q[key]=Q.get(key,W(0))+cv(v)*g**k
 L=[]
 for i in range(max((i for i,j in Q),default=-1)+1):
  L.append(trim([Q.get((i,j),W(0)) for j in range(max((j for k,j in Q if k==i),default=-1)+1)]))
 return L

def bs(U,P,s):
 return trim([ev(list(map(U,x)),s) for x in P])
def by(U,P,y):
 return sum_poly([sc(list(map(U,q)),y**j) for j,q in enumerate(P)])
def lifted(U,P):
 return [[U(w) for w in z] for z in P]

def poly_field(U,E0,E1,d):
 for T,S in [(E0,E1),(E1,E0)]+[(add(E0,sc(E1,k)),E1) for k in range(1,5)]:
  if len(T)!=d+1:continue
  try:T=mon(T)
  except ArithmeticError:continue
  V=Nested(T);y=V.gen()
  return V,y,ev(list(map(V,S)),y)
 raise ArithmeticError('unpreserved y projection degree')

def cand_depth(U,front,slot,branch,role,g,r,u,z,pegs,hh,forms,flags,anc,allowed):
 # h tail is known whenever a physical tail carries the Gauss double.
 Phi,E0,E1,T0,T1,D0= forms
 normR=r/g
 if branch==4: # row four is r, row five on singleton profile
  assert role!=4
  if role==5:
   s=normR;y=z
   eq1=ev(bs(U,E0,s),y);eq2=ev(bs(U,E1,s),y)
   return U,s,y,[eq1,eq2],pegs,hh
  s=normR
  EE,EF=bs(U,E0,s),bs(U,E1,s)
  power0=3
  if 'r' in flags:
   EE,rem=qr(EE,[-normR,U(1)]);assert not rem
   EF,rem=qr(EF,[-normR,U(1)]);assert not rem
   power0-=1
  V,y,e=poly_field(U,EE,EF,power0)
  return V,V(s),y,[e],list(map(V,pegs))+[V(g)*y],V(hh)
 if role==4:
  s=z;pc=ev(list(map(U,allowed if allowed is not None else Phi[0])),s)
  if conditional_zero(U,pc):return U,U(0),U(0),[U(1)],pegs,hh
  if branch==5:return U,s,normR,[pc,ev(bs(U,D0,s),normR)],pegs,hh
  V,y,e=poly_field(U,bs(U,T0,s),bs(U,T1,s),2)
  return V,V(s),y,[V(pc),e],list(map(V,pegs))+[V(g)*y],V(hh)
 M=trim(list(map(U,allowed if allowed is not None else Phi[0])))
 md=len(allowed)-1 if allowed is not None else (1 if 'lead' in flags else 2)
 assert len(M)==md+1,(len(M),md,flags)
 for k,q in (('r',normR),('a',anc)):
  if k in flags and allowed is None:
   M,rem=qr(M,[-q,U(1)]);assert not rem
   md-=1
 assert len(M)==md+1
 if md==0:
  M[0].inv()
  return U,U(0),U(0),[U(1)],pegs,hh
 S=Nested(mon(M));s=S.gen()
 if branch==5:
  y=S(normR)
  eq=ev(bs(S,D0,s),y)
  return S,s,y,[eq],list(map(S,pegs))+[S(g)*s],S(hh)
 if role==5:
  y=S(z)
  return S,s,y,[ev(bs(S,T0,s),y),ev(bs(S,T1,s),y)],list(map(S,pegs))+[S(g)*s],S(hh)
 V,y,e=poly_field(S,bs(S,T0,s),bs(S,T1,s),2)
 return V,V(s),y,[e],list(map(lambda h:V(S(h)),pegs))+[V(S(g))*V(s),V(S(g))*y],V(S(hh))

def moment_mask(F,pegs):
 D=nodal(pegs)
 if len(pegs)==6:return [intp(F,D),intp(F,D,1)]
 if len(pegs)==5:
  a,b,c=[intp(F,D,j) for j in range(3)]
  return [a*c-b*b]
 return []

def tail_known(F,g,r,anchor,u,rear,hit,silent):
 x=1-g;c=x-g*u;d=x-g*(2-u if rear else 2*u)
 K=Pcoeff(F,r)
 k=1+2*u-u*u
 H=F(1) if rear else -2+u+4*u*u-u**3
 Q=k if rear else -k*(4*u**3-12*u*u+3*u+2)
 px,pc,pd=[ev(K,j) for j in (x,c,d)]
 # All divisions below are only at a singleton nonterminal tail or the actual x clock.
 if silent:z=x+g*k*(u-2)/2
 else:
  v,j,l=(pd,d,Q) if hit==9 else (pc,c,k)
  hs=H if hit==9 else F(1)
  A=hs*v-l*px;B=hs*x*v-j*l*px
  z=B/A
 Z=z/g
 hz=F(0)
 if hit==9:hz=px*k*(c-z)/(x-z)
 if hit==8:hz=px*Q*(d-z)/(H*(x-z))
 pegs=[g*anchor,x]+([] if hit==9 else [c])+([] if silent or hit==8 else [d])+[r]
 return Z,hz,pegs

def add_mass(O,g,r,s,y,pegs,ah,anc,hh,H4,branch,aff):
 assert len(pegs)==4
 D=nodal(pegs);V,err=qr(D,[-r,O(1)]);assert not err
 a,b,c,d=[intp(O,D,j) for j in range(4)]
 V=mul(V,[b*d-c*c,b*c-a*d,a*c-b*b])
 v0,v1=intp(O,V),ev(V,r)
 p0=Pcoeff(O,r)
 D=ev(p0,g*anc)
 pp=ah*ev(p0,r)
 v=v1*intp(O,p0)/ev(p0,r)
 hh=hh*ah
 def mass(h):return v0*(pp-D*h)*(pp-hh)-v*pp*(pp-D*h-hh)
 if branch==4:return [mass(ev(H4,s))]
 Mt,Mh=mass(O(0)),mass(O(1))-mass(O(0))
 T0,A0,T1,A1=aff
 ht,ha=ev(bs(O,T0,s),y)*ev(H4,s),ev(bs(O,A0,s),y)*ev(H4,s)
 rt,ra=ev(bs(O,T1,s),y),ev(bs(O,A1,s),y)
 return [Mt*rt-Mh*ht,Mt*ra-Mh*ha]

def sixth(O,g,r,s,y,pegs,ah,anc,A,B,m,hh,H4,branch,aff):
 from both_front_silent8 import nextgate,context
 from one_front_zero import slopes
 h4s=ev(H4,s)
 ha,hb=(A-1)/2,(B-1-m)/2
 tr=A**3+A-1-A**4/4 if anc==A else B**3+B-1-m+m*A**3-B**4/4
 ar=ha if anc==A else hb+m*ha
 QT,QA=slopes(A,B,m,ha,hb,s,h4s,ar,tr,anc)
 L0,AA,e,_,_=context(O,A,B,m,ha,hb,None,H4)
 Q0=Pcoeff(O,r);P=[z*g**j for j,z in enumerate(Q0)]
 P=sc(P,ah/ev(P,anc))
 if branch==4:H5=ev(P,y)
 else:
  T0,A0,T1,A1=aff
  ab=[ev(bs(O,f,s),y) for f in (T0,A0,T1,A1)]
  h0,h1=ab[0]*h4s,ab[1]*h4s
  d0,d1=ab[2:]
  for j in range(10):
   try:
    H5=-(h0+j*h1)/(d0+j*d1);break
   except ArithmeticError:pass
  else:raise ArithmeticError('no actual h5 slope unit')
 G=nextgate(O,A,B,L0,e,TA=QT,QA=QA,C=P,Z=s,y=y,h=H5)
 D=nodal(pegs);a,b,c,d=[intp(O,D,j) for j in range(4)]
 Y=[b*d-c*c,(b*c-a*d)*g,(a*c-b*b)*g*g]
 if not Y[-1]:return O(0)
 while len(G)>=3:
  G=add(sc(G,Y[-1]),[O(0)]*(len(G)-3)+sc(Y,-G[-1]))
 G=G+[O(0)]*(2-len(G))
 l,m=G
 return Y[2]*l*l-Y[1]*l*m+Y[0]*m*m

def verify_other(f,slot,br,p,t):
 D0=core(f,slot)
 A0,B0n,m0=ends(f,1)
 al0=A0 if slot==0 else B0n
 hl0=(A0-1)/2 if slot==0 else (B0n-1-m0)/2
 ca0,cb0,ch0=[B0(Epoly(JJ(k))) if k else B0(0) for k in (al0, B0n if slot==0 else A0,hl0)]
 failures=[];nt=0
 for V,g,r,cv,flags,allowed in modparts(f,slot,br,p,t):
  nt+=1
  anc,off,ah=map(cv,(ca0,cb0,ch0))
  Vc=lambda an:cv(B0(Epoly(JJ(an)))) if an else V(0)
  a0,b0,tap0=map(Vc,(A0,B0n,m0))
  Phi,E0,E1,T0,T1,det0,*_=D0
  forms=[cast_poly(U,V,g,cv) for U in (Phi,E0,E1,T0,T1,det0)]
  row4h=[cv(w) for w in D0[8]]
  afs=[cast_poly(U,V,g,cv) for U in D0[13:17]]
  x=1-g
  for rear,h,silent in [(q,h,False) for q,h in product((True,False),(8,9))]+[(True,h,True) for h in (0,9)]:
   if h:
    F=V
    u=(x-r)/g
    if h==8:u=2-u if rear else u/2
   else:
    E=gap_polys(V,g,r,x,rear,silent)
    if len(E)!=4:failures.append(('gap-degree',rear,h,silent,len(E)-1));continue
    F=Tower(mon(E));u=F.gen()
   G,R,ancF,offF,ahF=map(F,(g,r,anc,off,ah))
   try:
    z,hh,pegs=tail_known(F,G,R,ancF,u,rear,h,silent)
   except ArithmeticError as e:
    failures.append(('tail pivot',rear,h,silent));continue
   for role in (0,) if silent else (0,4,5):
    if role==br and br!=0:continue
    try:O,s,y,eq,pegs0,h0=cand_depth(F,f,slot,br,role,G,R,u,z,pegs,hh,
                                      [lifted(F,v) for v in forms],flags,ancF,
                                      None if allowed is None else list(map(F,allowed)))
    except (ArithmeticError,TypeError,AssertionError,ValueError) as e:
     failures.append(('early pivot',rear,h,silent,role,repr(e)));continue
    extras=moment_mask(O,pegs0)
    if not extras and h and br and len(pegs0)==4:
     # O may be one or two exact monic extensions of F; preserve embedding order.
     def embed(v):
      if O is F:return F(v)
      if O.B is F:return O(F(v))
      return O(O.B(F(v)))
     HH=list(map(embed,row4h))
     fa=[[list(map(embed,c)) for c in A] for A in afs]
     extras=add_mass(O,embed(G),embed(R),s,y,pegs0,embed(ahF),embed(ancF),h0,HH,br,fa)
    try:span_unit(O,*eq,*extras)
    except ArithmeticError:
     if silent and h==9 and br==0 and len(pegs0)==5:
      def embed(v):return O(O.B(F(v)))
      aa,bb,mm,anc0,ah0=map(embed,(a0,b0,tap0,ancF,ahF))
      HH=list(map(embed,row4h))
      L1,L2=scaled_six(O,embed(G),embed(R),aa,bb,mm,anc0,ah0,s,y,pegs0,HH,h0)
      try:
       span_unit(O,*eq,*extras,L1)
       span_unit(O,*eq,*extras,L2)
       continue
      except ArithmeticError:pass
     if h and br and len(pegs0)==4:
      try:
       E6=sixth(O,embed(G),embed(R),s,y,pegs0,embed(ahF),embed(ancF),
                embed(a0),embed(b0),embed(tap0),h0,HH,br,fa)
       span_unit(O,*eq,*extras,E6)
       continue
      except ArithmeticError:pass
     failures.append(('moment',rear,h,silent,role,len(pegs0)))
 print('nong other',f,slot,br,nt,'nfail',len(failures),failures[:30],flush=True)
 return failures

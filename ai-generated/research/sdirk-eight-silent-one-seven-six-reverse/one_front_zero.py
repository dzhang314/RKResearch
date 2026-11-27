"""Detected independent Gauss double: one active literal front and k=0, x singleton."""
from both_front_active8 import *
from equal_undetected_front import Nested, lagrange

GF=Lf(G)
assert [(f.degree(),e) for f,e in GF.factor_list()[1]]==[(4,1)]
B0=ExField(Epoly(GF.monic()))
R0=B0(E(P([0,1])))
PX,rem=qr(list(map(B0,Lco)),[-R0,B0(1)])
assert not rem and len(PX)==4

def vals(F,f,z,rear,ori):
 cv=lambda x:F(Epoly(JJ(x))) if x else F(0)
 A,B,m=map(cv,ends(f,1))
 a,b,u0=map(cv,ends(True if rear is None else rear,ori))
 anc,sil=(A,B) if z==0 else (B,A)
 return A,B,m,anc,sil,a,b,u0

def physical(F,g,r,anc,a,b,rear,hit):
 X=1/g-1;C=1/g-a;D=1/g-b
 if hit=='0':
  assert g*anc==r
 if hit=='9':
  assert g*C==r
 if hit=='8':
  assert rear is not None and g*D==r
 ys=[('0',anc),('10',X),('9',C)] + ([] if rear is None else [('8',D)])
 if not hit:ys.append(('r',r/g))
 pegs=[h for j,h in ys]
 return X,C,D,pegs

def flags(F,g,r,anc,sil,a,b,rear,hit):
 x=1-g;c=1-g*a;d=1-g*b
 hs=[('0',g*anc),('9',c)] + ([] if rear is None else [('8',d)])
 forb=[g,x-r,x-g*sil,x-g*anc,Pphys(F,r,x)]
 for j,w in hs:
  if j!=hit:forb.append(w-r)
 if rear is not None:forb.extend([c-d,x-d,g*anc-d] if hit!='8' else [c-d,x-d])
 if hit!='9':forb.append(g*anc-c)
 if hit!='0':forb.append(Pphys(F,r,g*anc))
 return forb

def Pcoeff(F,r):
 P,rem=qr(list(map(F,Lco)),[-r,F(1)])
 assert not rem and len(P)==4
 return P
def Pphys(F,r,x):return ev(Pcoeff(F,r),x)

@lru_cache(None)
def g_projection(f,z,rear,ori,hit):
 U=B0
 A,B,m,anc,sil,a,b,rt=vals(U,f,z,rear,ori)
 u=a-1
 if hit:
  g={'0':R0/anc,'9':(1-R0)/a,'8':(1-R0)/b}[hit]
  if not all(flags(U,g,R0,anc,sil,a,b,rear,hit)):return [U(1)]
  G=[-g,U(1)]
 else:
  X=[U(1),U(-1)];C=[U(1),-a];D=[U(1),-b]
  G=add(subst(PX,C),sc(subst(PX,X),-2*u*u)) if rear is None else add(sc(subst(PX,D),u),sc(subst(PX,C),-(b-1-rt)))
  assert G
  # All guard factors: nonzero diagonal and exact exclusions defining this chart.
  G=strip(G,mul(mul([U(0),U(1)],[-U(1),U(1)+sil]),mul(add(X,[-R0]),mul(add(C,[-R0]),mul([-R0,anc],subst(PX,[U(0),anc]))))))
 print('exact diagonal degree',f,z,rear,ori,hit or 'none',len(G)-1,flush=True)
 return G

def slopes(A,B,m,ha,hb,Z,Hz,ah0,T0,anc):
 ta=(B*(Z-1-2*Hz)-(Z*Z/2-Z-2*Hz))/(B-A)
 tb=Z-1-2*Hz-ta
 TZ=Z**3-Z**4/4+2*Hz+ta*A**3+tb*B**3
 AZ=Hz+ta*ha+tb*hb
 Hanc=ha if anc==A else hb
 def line(zv,xv):
  m=(zv/Hz-xv/Hanc)/(Z-anc);return [xv/Hanc-anc*m,m]
 return line(TZ,T0),line(AZ,ah0)

def row5(F,A,B,Z,ha,hb,Hz,QT,QA,Hp):
 ns=[A,B,Z];hp=[ha,hb,Hz];cards=lagrange(ns)
 m0=add([F(-1),F(1)],sc(Hp,-2))
 m1=add([F(0),F(-1),F(1)/2],sc(Hp,-2))
 m2=add([F(0),F(0),F(-1),F(1)/3],sc(Hp,-F(4)/3))
 w=[sum_poly([sc(q,v) for q,v in zip([m0,m1,m2],p0)]) for p0 in cards]
 F1=sum_poly([[F(0),F(0),F(0),F(1),-F(1)/4],sc(Hp,2),sc(mul(QT,Hp),-1),
              *[sc(v,d**3) for v,d in zip(w,ns)]])
 F2=sum_poly([Hp,sc(mul(QA,Hp),-1),*[sc(v,d) for v,d in zip(w,hp)]])
 return F1,F2

def test_nonzero(*cs):
 for c in cs:
  try:c.inv();return
  except ArithmeticError:pass
 raise ArithmeticError('no unit')

def test_poly(Y,*cs):
 for c in cs:
  try:multicol(Y,c).inv();return
  except ArithmeticError:pass
 if len(Y)==2:raise ArithmeticError('linear nonunit')
 W=Nested(Y)
 test_nonzero(*[ev(list(map(W,c)),W.gen()) for c in cs])

def two_pivots(F,g,pegs):
 D=nodal([g*z for z in pegs]);J=lambda j:intp(F,D,j)
 a,b,c,d=[J(j) for j in range(4)];hh=a*c-b*b
 return [(b*d-c*c)/(hh*g*g),(b*c-a*d)/(hh*g),F(1)]

def sites(F,g,pegs):
 assert 4<=len(pegs)<=5
 if len(pegs)==4:return two_pivots(F,g,pegs)
 D=nodal([g*z for z in pegs]);J=lambda j:intp(F,D,j)
 a,b,c=[J(j) for j in range(3)]
 try:(a*c-b*b).inv();return []
 except ArithmeticError:return [-b/(a*g),F(1)]

def conditional_zero(F,x):
 # A necessary coefficient or projection, when a unit, contradicts the branch.
 try:x.inv();return True
 except ArithmeticError:return False

def copy_or_new(F,A,B,Z,ha,hb,Hz,QT,QA,Y,dup):
 a,b=row5(F,A,B,Z,ha,hb,Hz,QT,QA,[F(0)])
 c,d=row5(F,A,B,Z,ha,hb,Hz,QT,QA,[F(1)])
 e0,e1=ev(a,Y),ev(b,Y)
 u,v=ev(c,Y)-e0,ev(d,Y)-e1
 if dup:test_nonzero(u,v)
 else:test_nonzero(e0*v-e1*u)

def scalar_prep(f,z,rear,ori,hit,p,t):
 F=Bfield(nmod_poly(list(Lco),p),p,t)
 rr=F(nmod_poly([0,1],p))
 M0=g_projection(f,z,rear,ori,hit)
 G=list(map(F,M0))
 assert len(G)==len(M0) and G[-1]==1
 if len(G)<=1:return
 U=Tower(G);g=U.gen();r=U(rr)
 A,B,m,anc,sil,a,b,rt=vals(U,f,z,rear,ori);u=a-1
 for q in flags(U,g,r,anc,sil,a,b,rear,hit):
  # Guard units here; otherwise keep looking for a good specialization.
  q.inv()
 X,C,D,pegs=physical(U,g,r,anc,a,b,rear,hit)
 if hit=='0':
  s=Pphys(U,r,g*C)
  f0=s-2*u*u*Pphys(U,r,g*X) if rear is None else u*Pphys(U,r,g*D)-(b-1-rt)*s
  if conditional_zero(U,f0):return
 ha,hb=(A-1)/2,(B-1-m)/2
 H4=[U(Epoly(JJ(v))) for v in pol(h4(f),lambda v:v)]
 S=[q*g**j for j,q in enumerate(Pcoeff(U,r))]
 if hit!='0':
  S=sc(S,(ha if anc==A else hb)/ev(S,anc))
 R=r/g
 yield U,g,X,R,A,B,m,anc,ha,hb,S,H4,pegs

def do5(F,g,X,R,A,B,m,anc,ha,hb,S,H4,pegs,Z,Hp,Y,rx,allowx):
 tr=A**3+A-1-A**4/4 if anc==A else B**3+B-1-m+m*A**3-B**4/4
 ar=ha if anc==A else hb+m*ha
 QT,QA=slopes(A,B,m,ha,hb,Z,Hp,ar,tr,anc)
 # If the active front was the Gauss copy, S still has its unknown common scale.
 if anc==R:
  S=sc(S,Hp/ev(S,Z))
 F1,F2=row5(F,A,B,Z,ha,hb,Hp,QT,QA,S)
 if Y:test_poly(Y,F1,F2)
 if allowx:test_nonzero(ev(F1,X),ev(F2,X))
 if rx:copy_or_new(F,A,B,Z,ha,hb,Hp,QT,QA,R,rx==1)

def sparse_data(F,f,z,ori,g,r):
 A,B,m,anc,sil,a,b,rt=vals(F,f,z,None,ori)
 X=1/g-1;R=r/g
 ha,hb=(A-1)/2,(B-1-m)/2
 H4=[F(Epoly(JJ(v))) for v in pol(h4(f),lambda v:v)]
 S=[q*g**j for j,q in enumerate(Pcoeff(F,r))]
 S=sc(S,(ha if z==0 else hb)/ev(S,anc))
 return X,R,A,B,m,anc,ha,hb,S,H4
@lru_cache(None)
def sparse_exact(f,z,ori):
 G=g_projection(f,z,None,ori,'9')
 if len(G)<=1:return None
 g=-G[0]
 X,R,A,B,m,anc,ha,hb,S,H4=sparse_data(B0,f,z,ori,g,R0)
 assert R!=A and R!=B
 tr=A**3+A-1-A**4/4 if anc==A else B**3+B-1-m+m*A**3-B**4/4
 ar=ha if anc==A else hb+m*ha
 Hr=ev(H4,R)
 assert Hr
 QT,QA=slopes(A,B,m,ha,hb,R,Hr,ar,tr,anc)
 T,U=row5(B0,A,B,R,ha,hb,Hr,QT,QA,S)
 # Row five after the second active r must be an unpegged singleton.
 E=strip(gcdp(T,U),list(map(B0,nodal([anc,X,R]))))
 assert len(E)==1
 # Row four as a singleton can only be outside these three pegged clocks.
 Z=add(H4,sc(S,-1))
 assert not ev(Z,anc)
 return strip(Z,list(map(B0,nodal([anc,X,R]))))

def verify_sparse(f,z,ori,p,t):
 Z=sparse_exact(f,z,ori)
 if Z is None or len(Z)<=1:return True
 for U,g,X,R,A,B,m,anc,ha,hb,S,H4,pegs in scalar_prep(f,z,None,ori,'9',p,t):
  roots=list(map(U,[U.B(v) for v in Z]));assert roots[-1]==1
  W=Nested(roots);Z=W.gen()
  g,X,R,A,B,m,anc,ha,hb=map(W,(g,X,R,A,B,m,anc,ha,hb))
  S,H4=[list(map(W,q)) for q in (S,H4)]
  pegs=list(map(W,pegs))+[Z]
  Y=two_pivots(W,g,pegs)
  do5(W,g,X,R,A,B,m,anc,ha,hb,S,H4,pegs,Z,ev(H4,Z),Y,2,False)
 return True

def verify(f,z,rear,ori,hit,p,t):
 if rear is None and hit=='9':return verify_sparse(f,z,ori,p,t)
 for U,g,X,R,A,B,m,anc,ha,hb,S,H4,pegs in scalar_prep(f,z,rear,ori,hit,p,t):
  if len(pegs)<4:return 'sparse'
  Y=sites(U,g,pegs)
  if not Y:return True
  if len(Y)>1:
   W=Nested(Y);s=W.gen()
   cand=[W(a) for a in (g,X,R,A,B,m,anc,ha,hb)]
   sS,sH4=[list(map(W,q)) for q in (S,H4)]
   Hp=ev(sH4,s)
   if hit!='0' and conditional_zero(W,Hp-ev(sS,s)):pass
   else:
    ZY,r0=qr(list(map(W,Y)),[-s,W(1)]);assert not r0
    do5(W,*cand,sS,sH4,list(map(W,pegs)),s,Hp,ZY if len(ZY)>1 else [],
        1 if hit=='0' else 2,rear is not None)
  for Z in ([R] if hit!='0' else [])+([X] if rear is not None else []):
   Hp=ev(H4,Z)
   if Z==X and hit!='0' and conditional_zero(U,Hp-ev(S,Z)):continue
   rx=(0 if Z==R and hit in ('8','9') else (1 if Z==R or hit=='0' else 2))
   do5(U,g,X,R,A,B,m,anc,ha,hb,S,H4,pegs,Z,Hp,Y,rx,Z!=X and rear is not None)
 return True

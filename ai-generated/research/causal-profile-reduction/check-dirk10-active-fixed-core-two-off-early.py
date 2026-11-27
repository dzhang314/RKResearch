from itertools import permutations
import sys
from sympy import GF
from sympy.polys.fields import field
p=int(sys.argv[1]) if len(sys.argv)>1 else 419
I=tuple(v for v in range(p) if (42*v**4-84*v**3+56*v*v-14*v+1)%p==0)
assert len(I)==4
F,a=field('a',GF(p));R=F.ring

def d(a,b):
 if b%p==0:raise ZeroDivisionError
 return a*pow(b%p,-1,p)%p

def prod(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def nodal(ns):
 c=[1]
 for z in ns:c=prod(c,[-z,1])
 return c

def val(P,x): return sum(v*x**i for i,v in enumerate(P))
def IP(P,x): return sum(c*x**(i+1)*d(1,i+1) for i,c in enumerate(P))
def prim(ns,x):return IP(nodal(ns),x)

M={t:prim([s for s in (0,*I,1) if s!=t],1)%p for t in I}

def vals(U,W,R):
 return {
  U:d(-U**3,6),
  W:d(W**3*(2*U-W),6*(U-2*W)),
  R:d(R**3*(2*U-W)*(3*R*R-5*R*(U+W)+10*U*W),6*(4*R*U*U-13*R*U*W+4*R*W*W+U*U*W+U*W*W)),
 }

def Fcoeff(t):
 H=[0,1,-14,56,-84,42]; f=[0]*5; f[-1]=42
 for i in range(3,-1,-1):f[i]=(H[i+1]+t*f[i+1])%p
 assert (t*f[0])%p==0
 return f

bad=[]; survives=[]; altbad=[]; passed_early=0; extra=[]; details=[]
for U,W,Rr,X in permutations(I):
 try:
  E={t:d(M[t]*k,t) for t,k in vals(U,W,Rr).items()}
  Z=d(10*Rr*U*U-25*Rr*U*W+10*Rr*W*W+U*U*W+U*W*W,6*(U-W)**2)
 except ZeroDivisionError:bad.append(('rev',U,W,Rr,X));continue
 x=(1-X)%p
 for V in (W,Rr,X):
  t=(1-V)%p
  try:
   v2=(Rr if W==V else W)
   D=(E[v2]-E[U])%p
   aS=d(E[v2]*v2-E[U]*U,D)
   bP=d(E[U]*U*U-E[v2]*v2*v2,D)
   # P=aS*S+bP. For actual off a,b, ab=d0+d1(a+b).
   d0=(bP+2*aS-1)%p; d1=(1-aS)%p
   fc=Fcoeff(t)
   if V==X:
    assert v2==W
    S=d(E[U]*U*U-E[Rr]*Rr*Rr+(E[U]-E[Rr])*bP,(E[U]*U-E[Rr]*Rr)-(E[U]-E[Rr])*aS)
    P=(aS*S+bP)%p
    assert (E[Rr]*(Rr*Rr-S*Rr+P)-E[U]*(U*U-S*U+P))%p==0
    sa0=(2-S)%p; ab=(1-S+P)%p
    b=sa0-a
    Q=a*a-sa0*a+ab
   else:
    # Guard a−d1 cannot vanish iff d0+d1² is nonzero.
    if not (d0+d1*d1)%p:bad.append(('mobius factor',U,W,Rr,X,V,d0,d1));continue
    Q=None
    b=(d1*a+d0)/(a-d1)
  except ZeroDivisionError:bad.append(('det',U,W,Rr,X,V));continue
  sa=-val(fc,a);sb=-val(fc,b)
  phaseA=a**3*(a-2*b)*sb+b**3*(2*a-b)*sa
  clean=nodal([0,t,a,b]); pxi=IP(clean,t); pa=IP(clean,a); pb=IP(clean,b);
  LNnum=-pa*sb*(b-t)-pb*sa*(t-a); LNden=sa*sb*(b-a)
  absentBefore=t**3*(2*a-t)*sa*LNnum-pxi*a**3*(a-2*t)*LNden
  if V==X:
   gg=[Q.numer.gcd(k.numer) for k in (absentBefore,phaseA)]
   if any(h.degree()>0 for h in gg):survives.append(('V=X',U,W,Rr,X,V,gg,Q.numer))
   details.append((U,W,Rr,X,V,'pinned',gg))
   continue
  Dd=a-d1; Bb=d1*a+d0; T=Bb-a*Dd
  rho=(d0+d1*d1)%p
  Ca=val(fc[1:],a)
  Cb=sum(cc*Bb**ii*Dd**(3-ii) for ii,cc in enumerate(fc[1:]))
  PA=10*t*Bb-5*(t*Dd+Bb)*a+3*a*a*Dd
  PB=10*t*a*Dd**2-5*(t+a)*Bb*Dd+3*Bb**2
  PV=10*a*Bb-5*(a*Dd+Bb)*t+3*t*t*Dd
  MN=(a*a*PA*Cb*(Bb-t*Dd)+Bb*Bb*PB*Ca*(t-a)*Dd)/T
  nXi=prim([0,x,a,b],x)*Dd
  vXi=t*(t-x)*(t-a)*(t*Dd-Bb)
  Bsum=-IP(fc,x)*vXi+nXi*val(fc,t)
  PBef=a*a*(a-2*t)*Bsum+t**3*(2*a-t)*Ca*nXi
  ABef=(2*a-t)*MN+a*a*(a-2*t)*PV*Cb
  PAft=(a*a*(a*Dd-2*Bb)*Cb+Bb*Bb*(2*a*Dd-Bb)*Ca*Dd)/T
  AAft=MN*Bsum-t**3*PV*nXi*Ca*Cb
  assert all(v0.denom.degree()==0 for v0 in (MN,nXi,PBef,ABef,PAft,AAft))
  r0,s0=(1-U)%p,(1-v2)%p
  assert r0!=s0 and {r0,s0}==set(I)-{x,t}
  assert (d1*t+d0-t*(t-d1))%p
  q2=(a-r0)*(a-s0); q3=q2*(a-t)
  A1,A2=PAft/q2,AAft/q2
  B1,B2=PBef/q3,ABef/q3
  for pp,deg in [(A1,4),(A2,8),(B1,3),(B2,6)]:
   assert pp.denom.degree()==0 and pp.numer.degree()==deg, (U,W,Rr,X,V,pp,deg)
  ga=A1.numer.gcd(A2.numer);gb=B1.numer.gcd(B2.numer)
  if ga.degree() or gb.degree():survives.append(('V!=X',U,W,Rr,X,V,ga,gb))
  passed_early+=1
  details.append((U,W,Rr,X,V,PAft.numer.degree(),AAft.numer.degree(),PBef.numer.degree(),ABef.numer.degree()))
print(p,I,'bad',len(bad),'surv',len(survives),'altbad',len(altbad),'passed_early',passed_early,'details',len(details))
print('degrees',set(tuple(k[5:]) for k in details if len(k)==9)); print('bad',bad);print('survives',survives);print('altbad',altbad[:12]);
assert not bad and not survives and len(details)==72 and passed_early==48

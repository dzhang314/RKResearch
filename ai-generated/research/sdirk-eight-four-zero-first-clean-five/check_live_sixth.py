#!/usr/bin/env python3
from itertools import permutations
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from math import lcm
def peel(G,D):
 while G.degree()>0:
  x=G.gcd(D)
  if x.degree()<=0:break
  G,r=divmod(G,x);assert r.is_zero()
 return G
def solve(F,R,U,p,mode,ga,a,xd):
 O=F.one();Z=F.zero()
 val=lambda P,c:sum((r*c**i for i,r in enumerate(P)),R.zero())
 J=lambda P,c:sum((r*c**(i+1)/(i+1) for i,r in enumerate(P)),R.zero())
 IJ=lambda P,c:sum((r*c**(i+2)/(i+2) for i,r in enumerate(P)),R.zero())
 homog=lambda P,m,N,D:sum((r*N**i*D**(m-i) for i,r in enumerate(P)),R.zero())
 k=1+2*U-U*U
 if mode=='S':
  H=R.one();j=R.zero();Rgn=U*(U-1)*(U-2)*k
  xs=[R.one(),1+U,3-U]
 else:
  H=-2+U+4*U**2-U**3;j=3*U-2
  Rgn=U*k*H*j*(H*(1+4*U-4*U**2)+4*U**2*j)
  xs=[R.one(),1+U,1+2*U]
 P=[j*(1+U),H-j*(2+U),-H/2+j]
 r=[R.one()]
 for x in xs:r=[-x*r[0]]+[r[i-1]-x*r[i] for i in range(1,len(r))]+[r[-1]]
 D=val(P,a)-J(P,a);N=a*val(P,a)-IJ(P,a)
 C=D.gcd(N)
 assert not C.is_zero()
 C=peel(C,Rgn)
 if C.degree()>0:return 0,0,[('singular D=N=0',C)]
 if D.is_zero():return 0,0,[]
 rho=[P[0],P[1]-P[0],P[2]-P[1]/2,-P[2]/3]
 sig=-3*H*(N-D)+3*k*P[1]*D+(4*k*D+2*(k+1)*(N-D))*P[2]
 B=J(r,a)-val(r,a)
 G=B*(3*k*H*homog(rho,3,N,D)-sig*homog(P,2,N,D))-homog(r,3,N,D)*sig
 assert not G.is_zero()
 E=peel(G,Rgn*D)
 # Traces with convenient denominator-free scalar factors.
 rp1=[D*x+B*y for x,y in zip(r,P+[R.zero()])]
 rp2=[N*P[0],N*P[1]-D*P[0],N*P[2]-D*P[1],-D*P[2]]
 # V1 = D R - B H (g-P/H), V2 = (N-DX)(P-Hg).
 gh1=[-B*H,R.zero()]
 gh2=[-N*H,D*H]
 aa1,aa2=val(rp1,a),val(rp2,a)
 hp=[aa2*x-aa1*y for x,y in zip(rp1,rp2)]
 hgf=[aa2*x-aa1*y for x,y in zip(gh1,gh2)]
 def L(x):return 70*x**4-140*x**3+90*x*x-20*x+1
 ct=sn=0;out=[]
 for f,m in E.factor()[1]:
  ct+=1
  def red(z):return (R([z]) if not hasattr(z,'degree') else z)%f
  def div(z,w):
   w=red(w)
   assert not w.is_zero()
   return red(red(z)*w.inverse_mod(f))
  x4=div(N,D)
  if red(sig).is_zero():
   sn+=1
   if not red(homog(rho,3,N,D)).is_zero():continue
   if red(B).is_zero():
    if red(val(r,x4)).is_zero():out.append(('singular free g4',f,x4))
    continue
   g4=red(div(val(P,x4),H)+div(D*val(r,x4),H*B))
  else:
   g4=div(3*k*homog(rho,3,N,D),D**2*sig)
  if g4.is_zero() or red(g4*H-val(P,x4)).is_zero():continue
  xx=[*(red(x) for x in xs),x4];gg=[*(div(val(P,x),H) for x in xs),g4]
  def interp(zs,x):
   ans=R.zero()
   for i,t in enumerate(xx[:3]):
    a0=zs[i]
    for j,s in enumerate(xx[:3]):
     if i!=j:a0=div(a0*(x-s),t-s)
    ans=red(ans+a0)
   return ans
  def gv(vals,x):
   # The first three sites give q0; g-P/H is its missing fourth pivot.
   coeff=div(vals[3]-interp(vals[:3],x4),g4-div(val(P,x4),H))
   return coeff,red(interp(vals[:3],x)-coeff*div(val(P,x),H))
  q,q0=gv([div(-J(hp,x),g) for x,g in zip(xx,gg)],red(xd))
  ld=red(L(ga*xd))
  assert not ld.is_zero()
  l,l0=gv([div(L(ga*x),g) for x,g in zip(xx,gg)],red(xd))
  ff=[red(J(hp,xd)-val(hp,xd)),red(q0-val(hgf,xd)),q]
  hh=[-ld,l0,l]
  def trim(P):
   while P and P[-1].is_zero():P=P[:-1]
   return P
  def rem(A,B):
   A=trim(A);B=trim(B)
   while len(A)>=len(B):
    s=div(A[-1],B[-1]);m=len(A)-len(B)
    for i,b in enumerate(B):A[m+i]=red(A[m+i]-s*b)
    A=trim(A)
   return A
  ff=trim(ff);hh=trim(hh)
  while hh:ff,hh=hh,rem(ff,hh)
  if len(ff)>1:out.append(('live sixth',f,ff))
 return ct,sn,out

for p in (13,17,103,131,7793):
 ds=lcm(*(f.degree() for f,e in nmod_poly([3,0,-30,0,35],p).factor()[1]))
 F=fq_default_ctx(p,ds,'w');R=fq_default_poly_ctx(F);U=R.gen();O=F.one();Z=F.zero()
 gs=[x for x,e in (35*U**4-30*U**2+3).roots()]
 ks=[x for x,e in (U**2-2*U-1).roots()]
 assert len(ks)==2
 cnt=nc=0;out=[]
 for y,z in permutations(gs,2):
  for v in ks:
   for ph,b in (('arith',1+2*v),('star',3-v)):
    if b*(1+y)!=(1+v)*(1+z):continue
    ga=(1+y)/(2*(1+v));d=1-ga
    for aa in gs:
     if aa in (y,z):continue
     a=(1+aa)/(2*ga)
     for mode in ('S','A'):
      n,ns,L=solve(F,R,U,p,mode,ga,a,d/ga)
      cnt+=n;nc+=ns
      if L:out.append((p,y,z,v,a,mode,L))
 assert not out and cnt=={13:28,17:14,103:11,131:28,7793:19}[p]
 assert nc==(2 if p==17 else 0)
 print(p,cnt,"irreducible opening factors, including",nc,"singular sigma",flush=True)

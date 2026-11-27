"""No-front k!=0, arithmetic tail, all three tail clocks singletons."""
from no_front_nonzero import *
from flint import fmpq_mpoly_ctx
ctx=fmpq_mpoly_ctx.get(['g','u','r','t'])
g,u,r,t=ctx.gens()

def coefficients(F):
 R={}
 for (i,j,k,l),q in F.to_dict().items():
  H=R.setdefault(j,{}).setdefault(i,[[],[]])
  D=H[l%2]
  D.extend([Q(0)]*(k+1-len(D)))
  D[k]+=q/(2**(l//2))
 z=[]
 for j in range(max(R,default=-1)+1):
  H=R.get(j,{})
  z.append(trim([B0(E(*map(P,H.get(i,([],[]))))) for i in range(max(H,default=-1)+1)]))
 return z

def qp(x):
 return sum(q*x**j for j,q in enumerate([-20+90*r-140*r*r+70*r**3,90-140*r+70*r*r,-140+70*r,70]))

def raw_arm(front,zslot):
 Z0=2+2*t if zslot==0 else (2-2*t if front else 3+4*t)
 x,z=1-g,g*Z0;c,d=1-g*(1+u),1-g*(1+2*u)
 H=-2+u+4*u*u-u**3; k=1+2*u-u*u; C3=4*u**3-12*u*u+3*u+2
 F,er=divmod((x-z)*qp(c)-k*(c-z)*qp(x),u);assert not er
 J,er=divmod(H*(c-z)*qp(d)+C3*(d-z)*qp(c),u);assert not er
 return F,J,(x,z,c,d,H,k,C3)

def ptrim(A):
 while A and not A[-1]:A=A[:-1]
 return A
def pseudo(a,b):
 assert a and b
 xr=b[-1]
 while len(a)>=len(b):
  m=len(a)-len(b); ar=a[-1]
  a=ptrim([add(mul(v,xr),sc(mul(b[i-m],ar),-1) if m<=i<m+len(b) else []) for i,v in enumerate(a)])
 return a

def redcoprime(a,b):
 # Exact coprimality from preserved degrees at one fixed good reduction.
 for p,t0 in ((1009,285),(1129,203)):
  F,rr=mod_base(p,t0)
  try:
   A,B=list(map(F,a)),list(map(F,b))
   A[-1].inv();B[-1].inv()
   if len(gcdp(A,B))==1:return True
  except (ArithmeticError,ValueError,ZeroDivisionError):
   pass
 return False

def guarded(a,bs):
 for b in bs:
  assert b
  while len(b)>1 and len(a)>1 and not redcoprime(a,b):
   # First reduce the larger polynomial by the smaller exact polynomial.
   D=gcdp(a,b)
   if len(D)==1:break
   a,rem=divp(a,D);assert not rem
 return a

@lru_cache(None)
def generic(front,zslot):
 F0,J0,guards=raw_arm(front,zslot)
 F,J=map(coefficients,(F0,J0))
 assert len(F)==3 and len(J)==6
 a,b,c=F
 # If u polynomial loses its quadratic term, inspect that finite locus separately.
 a,b,c=map(trim,(a,b,c))
 L=pseudo(J,F)
 assert len(L)==2
 l,m=L
 # Remove a common polynomial factor which is a unit in the main open pivot sector.
 hh=gcdp(l,m)
 assert len(hh)>0
 l,lr=divp(l,hh);m,mr=divp(m,hh);assert not lr and not mr
 hh=guarded(hh,[c])
 print('F degrees',list(map(lambda q:len(q)-1,F)),'prem degrees',len(l)-1,len(m)-1,'common',len(hh)-1,flush=True)
 Res=sum_poly([mul(c,mul(l,l)),sc(mul(b,mul(l,m)),-1),mul(a,mul(m,m))])
 print('raw res deg',len(Res)-1,flush=True)
 _,_,_,Z=phase(B0,front,zslot)
 xg=[B0(1),B0(-1)]
 zg=[B0(0),Z]
 vb=[[B0(0),B0(1)], add(xg,sc(zg,-1)), add(xg,[-R0]), add(zg,[-R0]), subst(PX,xg),subst(PX,zg)]
 Mi=guarded(Res,[c,m,*vb])
 print('generic clean deg',len(Mi)-1,flush=True)
 # Saturate against u-only/lead-adjusted known physical guards using u=-l/m.
 def at_frac(T):
  T=coefficients(T)
  n=len(T)-1
  return sum_poly([mul(mul(power(sc(l,-1),j),power(m,n-j)),v) for j,v in enumerate(T)])
 x,z,c1,d,H,k,C3=guards
 for name,v in [('u',u),('k',k),('H',H),('C3',C3),('c-z',c1-z),('d-z',d-z),('c-r',c1-r),('d-r',d-r),('p(c)',qp(c1)),('p(d)',qp(d))]:
  Mi=guarded(Mi,[at_frac(v)])
  print('guard',name,len(Mi)-1,flush=True)
 # Special pivot sites. A solution either in generic Mi or one of these guarded projections.
 intrinsic=vb
 if len(hh)>1:hh=guarded(hh,intrinsic)
 Jlead=guarded(c,intrinsic)
 print('exceptional pivot degrees',len(hh)-1,len(Jlead)-1,flush=True)
 return mon(Mi),l,m,hh,mon(Jlead),F,J

def precheck(front,zslot,p,t0):
 M,l,m,hh,lead,F,J=generic(front,zslot)
 assert len(hh)==1 # at least one linear remainder coefficient at every nonzero quadratic pivot
 V,Rm=mod_base(p,t0)
 a,b,c=F
 if len(lead)>1:
  W=Tower(list(map(V,lead)));gg=W.gen()
  at=lambda q:ev(list(map(W,q)),gg)
  assert not at(c)
  if not conditional_zero(W,at(b)):
   # All linear pivots are required at this fixed reduction.
   raise ArithmeticError('leading-exception linear pivot failed')
  uu=-at(a)/at(b)
  # The remaining literal two-tail equation excludes this finite exceptional locus.
  ev([at(q) for q in J],uu).inv()
 if len(M)>1:
  W=Tower(list(map(V,M)));gg=W.gen()
  at=lambda q:ev(list(map(W,q)),gg)
  at(c).inv();at(m).inv()
  uu=-at(l)/at(m)
  assert not ev([at(q) for q in F],uu)
  assert not ev([at(q) for q in J],uu)
  front_core(W,W(Rm),gg,uu,front,zslot,False,0)
 return True

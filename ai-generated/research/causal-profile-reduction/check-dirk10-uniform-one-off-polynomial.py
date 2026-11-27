from itertools import permutations
from sympy import GF
from sympy.polys.fields import field
import sys
p=int(sys.argv[1]) if len(sys.argv)>1 else 419
F,q=field('q',GF(p)); R=F.ring; Q=R.gens[0]
I=tuple(v for v in range(p) if (42*v**4-84*v**3+56*v*v-14*v+1)%p==0)
assert len(I)==4

def H(x):return x*(42*x**4-84*x**3+56*x*x-14*x+1)
def poly(nodes):
 c=[F.one]
 for v in nodes:c=[(c[i-1] if i else F.zero)-v*(c[i] if i<len(c) else F.zero) for i in range(len(c)+1)]
 return c

def ip(c,x):return sum(v*x**(i+1)/(i+1) for i,v in enumerate(c))
def prim(nodes,x):return ip(poly(nodes),x)
def exact(a,d):
 z=a/d
 if z.denom.degree():raise ValueError('nonpoly',z)
 return z

def cop(a,b,context):
 g=a.numer.gcd(b.numer)
 if g.degree():raise ValueError('not-coprime',context,g)

def subq(f,y): return F(f.numer.evaluate(y))/F(f.denom.evaluate(y))
for x0 in I:
 x=F(x0)
 q0=x*(5-3*x)/(10-5*x)
 assert q0 not in (0,1,*I)
 assert (1-2*q0)*H(q0)/q0+q0**3*(2-q0)
 for y in (0,q0,1,x):
  others=tuple(z for z in (F.zero,q0,F.one,x) if z!=y)
  assert prim(others,x)
print(p,'zero common root fine')
Ds=[]
for t0,x0 in permutations(I,2):
 t,x=F(t0),F(x0); b=F.one; z=F.zero
 Ft=exact(H(q),q-t); Ct=exact(Ft,q)
 coeff=[0,1,-14,56,-84,42]; QF=[F.zero]*5;QF[-1]=F(42)
 for i in range(3,-1,-1): QF[i]=coeff[i+1]+t*QF[i+1]
 r=ip(QF,x); ft=sum(v*t**i for i,v in enumerate(QF))
 nt=prim((z,q,b,x),x); nq=prim((z,t,b,x),x); n1=prim((z,t,q,x),x)
 pt=prim((z,t,q,b),t); p1=prim((z,t,q,b),b)
 Cp=-(10*t-5*(t+1)*q+3*q*q)/60; pq=q**3*Cp
 # qCore: τ is first head a, 1 is b; hard exceptional tests first.
 k0=t*(t-1)*(t-x); K=r*k0*(t-q)-ft*nt
 assert r and nq and all(v.numer.degree()==1 for v in (nt,n1,pt,K))
 cop(nt,pt,('S_tau=0 requires p_tau=0',t,x))
 cop(pt,K,('p_tau=0 forces live hτ',t,x))
 cop(pt,n1,('p_tau=0 forces 1 present',t,x))
 node=(q-t)*p1*Ft-pq
 cop(pt,node,('p_tau=0 absent residual',t,x))
 s1=F(-1)/(1-t); st=K/nt
 A=exact(Ft*((1-t)*K*(q-t)*p1-(1-q)*pt*nt)-(1-t)*K*pq,q*(q-t)*(q-1))
 for y,w in ((t,b),(b,t)):
  sy=st if y==t else s1; sw=s1 if w==b else st
  raw1=y**3*(y-2*q)*Ct-q*q*(2*y-q)*sy
  raw2=y**3*(y-2*w)*sw+w**3*(2*y-w)*sy
  C=exact(raw1*nt,1) if y==t else raw1
  Aft=raw2*nt
  assert Aft.denom.degree()==0
  cop(A,C,('true core before',t,x,y));cop(A,Aft,('true core after',t,x,y))
  if y==t:cop(n1,C,('absent unit head',t,x))
  Ds.append(('core',y==t,A.numer.degree(),C.numer.degree(),Aft.numer.degree()))
 # qHead with ξ=1: virtual endpoint copies all dirty except terminal.
 End0=K*(q-1)*(q-x)+k0*nq*Ct
 BeforeT=t**3*(t-2)*nt-(2*t-1)*(1-t)*K
 BeforeQ=q*q*(q-2)+(2*q-1)*(1-t)*Ct
 After=q*q*(q-2*t)*K-t**3*(2*q-t)*Ct*nt
 cop(n1,A,("endpoint zero-tap changed core by absent column",t,x))
 for G,target in ((BeforeT,1),(BeforeQ,4),(After,5)):
  assert G.numer.degree()<=target
  cop(A,G,('endpoint core timing',t,x))
 # qHead: ξ=t, heads q and 1.
 B2=exact(-nq*Ct+n1*(q-t)*(q-x)/((1-t)**2*(1-x)),(q-1)*(q-x))
 Ee=exact(q*q*Cp+(t-q)*p1*Ct,q-1)
 Ah=exact((1-t)*k0*Ee*B2-Ct*nt*pt,q-t)
 cop(nt,pt,('n_core=0 forces p_core nonzero',t,x))
 cop(nt,B2,('n_core=0 head payment',t,x))
 cop(pt,n1,('p_core=0 unit head present',t,x))
 cop(pt,Ee,('p_core=0 absent ell nonzero',t,x))
 cop(pt,B2,('p_core=0 head payment',t,x))
 cop(n1,nt,('missing unit head core tap',t,x))
 for y,w in ((q,b),(b,q)):
  sy=-Ft if y==q else s1; sw=s1 if w==b else -Ft
  D=k0*y**3*(y-2*t)*B2+t**3*(2*y-t)*sy*nt
  Z=y**3*(y-2*w)*sw+w**3*(2*y-w)*sy
  den=q if y==q else F.one # every after polynomial includes q because one head degree-1 amplitude. handle both below
  D=exact(D,den); Z=exact(Z,q)
  cop(Ah,D,('head before',t,x,y));cop(Ah,Z,('head after',t,x,y))
  if y==q:cop(n1,D,('head absent 1',t,x))
  Ds.append(('head',y==q,Ah.numer.degree(),D.numer.degree(),Z.numer.degree()))
print(p,I,'ALL VALID',set(Ds))

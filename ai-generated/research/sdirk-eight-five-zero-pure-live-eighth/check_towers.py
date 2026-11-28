#!/usr/bin/env python3
import sympy as S
from sympy.polys.rings import ring
from time import monotonic
us=S.symbols('u')
Q=us**3-3*us**2+S.Rational(3,4)*us+S.Rational(1,2)
assert S.Poly(Q,us).is_irreducible
K=S.QQ.algebraic_field((S.Poly(Q,us),us));R,V,D=ring('v,D',K);u=K.unit
def now(*x):print(round(monotonic()-t0,2),*x,flush=True)
t0=monotonic()
one=R.one;zero=R.zero
kdiv=lambda a,d:a*K.convert(S.Rational(1,d))
def add(P,Q):
 return [(P[i] if i<len(P) else zero)+(Q[i] if i<len(Q) else zero) for i in range(max(len(P),len(Q)))]
def mul(P,Q):
 A=[zero for i in range(len(P)+len(Q)-1)]
 for i,p in enumerate(P):
  for j,q in enumerate(Q):A[i+j]=A[i+j]+p*q
 return A
def con(a):return [a]
scale=lambda P,a:[t*a for t in P]
def verify_fiber(SD,M,PS,m0):
 Y=SD.gens[0]
 SZ=SD.zero;SO=SD.one
 def trim(A):
  while A and not A[-1]:A=A[:-1]
  return A
 def ev_in_v(P):
  A=[SZ]*(1+P.degree(V)) if P else []
  for (j,k),c in P.items():A[j]+=Y**k*c
  return trim([a%M for a in A])
 def inv(a):
  s,t,g=a.gcdex(M)
  assert g==SO and a*s+t*M==SO
  return s%M
 def rem(P,Q):
  P=list(P);z=inv(Q[-1])
  while len(P)>=len(Q):
   k=len(P)-len(Q);a=(P[-1]*z)%M
   for j,q in enumerate(Q):P[j+k]=(P[j+k]-a*q)%M
   P=trim(P)
  return P
 def gcd(P,Q):
  while Q:P,Q=Q,rem(P,Q)
  if not P:return []
  a=inv(P[-1]);return [(a*x)%M for x in P]
 F=[]
 for P in PS:F=gcd(F,ev_in_v(P))
 assert len(F)==2 and F[-1]==SO
 assert not rem(ev_in_v(m0),F)
 now('D degree',M.degree(),'monic rear linear gcd; M0 remainder zero')

def prog(phase):
 A=one*(1+2*u)
 if phase=='star':
  # V=(v-1)^2, symmetric reflected star clocks, direct known third terminal.
  P=mul(mul([-A,one],[-(D-1),one]),[(D-2)**2-V,-2*(D-2),one])
 else:
  P=[one]
  for r in [A,D-1,D-1-V,D-1-2*V]:P=mul(P,[-r,one])
 M=[sum((kdiv(q*D**j,i+j+1) for j,q in enumerate(P)),zero) for i in range(4)]
 m0,m1,m2,m3=M
 f1=m0*m2-m1*m1;f2=m0*m3-m1*m2
 r=mul([-one,one],[-one*(1+u),one]); J=lambda P:[zero]+[kdiv(p,i+1) for i,p in enumerate(P)]
 def ev(P,x):return sum((p*x**j for j,p in enumerate(P)),zero)
 j0,j1=J(r),J([zero]+r)
 L=[D**4,-20*D**3,90*D**2,-140*D,70*one]
 q0=add(add(scale(j0,A),scale(j1,-one)),mul([-A,one],r))
 q1=A*ev(r,A)-ev(j1,A)
 G=add(scale(q0,ev(L,A)),scale(L,-q1))
 f3=sum((row*(D*m1)**i*m0**(4-i) for i,row in enumerate(G)),zero)
 fs=[f1,f2,f3]
 def guard(F):
  # Dividing out only powers of D is legitimate here.
  while F and all(j>0 for (i,j) in F.monoms()):F=F//D
  return F
 fs=[guard(f) for f in fs]
 now(phase,'degrees',[(f.degree(V),f.degree(D),len(f)) for f in fs])
 Rs=[]
 for i,j in [(0,1),(0,2),(1,2)]:
  w=fs[i].resultant(fs[j])
  now(phase,'resultant',i,j,w.degree(),len(w))
  Rs.append(w)
 g=Rs[0].gcd(Rs[1]).gcd(Rs[2])
 now(phase,'gcd','degree',g.degree(),'converted',g.as_expr())
 SD=g.ring
 facts=g.factor_list()[1]
 x=SD.gens[0]
 f=SD.one
 for M,e in facts:f*=M**e
 assert f==g.monic()
 assert [(M.degree(),e) for M,e in facts]==([(1,4),(5,1)] if phase=='star' else [(1,8),(2,1),(8,1)])
 assert facts[0][0]==x
 now(phase,"factor degrees",[(M.degree(),e) for M,e in facts])
 for fac,e in facts[1:]:verify_fiber(SD,fac,fs,m0)

for phase in ('star','arithmetic'):
 prog(phase)

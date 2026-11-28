#!/usr/bin/env python3
"""Integer-primitive regular no-midpoint projection, with all anchors."""
from math import gcd,lcm
from flint import fmpq_poly,fmpq_mpoly_ctx
import chart as E
k,q,g,y=E.k,E.q,E.g,E.y
C=E.C
A,B,T=E.A,E.B,E.T
sub=lambda f:E.substitute_diagonal(f,B,180*A)
p0=E.p0
fixed=(2,3,5,7)
def stripped(x):
 if not x:return 0
 for p in fixed:
  while x%p==0:x//=p
 return x
def scale(p,pr=False,ck=True):
 cs=list(p.terms());N=lcm(*(int(c.denominator) for e,c in cs))
 if ck:assert stripped(N)==1,(N,'bad denominator')
 a={e:int(c*N) for e,c in cs}
 if pr:
  s=gcd(*(abs(d) for d in a.values()))
  if s:a={e:v//s for e,v in a.items()}
 return p.context().from_dict(a)
def trim(F,G):
 F=scale(F)
 while F:
  h=F.gcd(G)
  if h.is_constant():break
  h=scale(h,True,False)
  assert all(c.denominator==1 for c in (G/h).coeffs())
  F=F/h
  assert all(c.denominator==1 for c in F.coeffs())
 return F
two=fmpq_mpoly_ctx.get(('k','q'))
slow=lambda p:p.project_to_context(two)
kk,qq=two.gens()
mir=lambda p:p.compose(-kk,qq)
G=scale(slow(sub(E.R*E.mirror(E.R))*sub(E.D*E.mirror(E.D))*sub(E.U*E.mirror(E.U))*A*T*B*k*p0))
F,Q,pin,H=[trim(slow(sub(p)),G) for p in (E.F,E.G,E.pin,E.anchor)]
def pair(p):
 return (p+mir(p))/2,(p-mir(p))/(2*kk)
sq=fmpq_mpoly_ctx.get(('x','q'))
def cv(p):
 assert all(a%2==0 for (a,_),_ in p.terms())
 return sq.from_dict({(a//2,b):c for (a,b),c in p.terms()})
def scalar(P):
 cs=P.context().names();n=cs.index('q')
 nr=max((e[n] for e,c in P.terms()),default=-1)
 C0=[0]*(nr+1)
 for e,c in P.terms():
  assert all(v==0 for j,v in enumerate(e) if j!=n)
  C0[e[n]]=c
 return fmpq_poly(C0)
def prim(P):
 L=lcm(*(int(c.denominator) for c in P.coeffs()))
 vals=[int(c*L) for c in P.coeffs()]
 d=gcd(*vals)
 return fmpq_poly([c//d for c in vals]) if d else P
out={}
for tag in ('AA','AZ','ZZ'):
 if tag=='AA':
  py=[cv(trim(v,scale(G*mir(G)))) for p in (F,H) for v in pair(p)]
  var='x'
 elif tag=='ZZ':
  py=[cv(trim(v,scale(G*mir(G)))) for p in (Q,pin,H) for v in pair(p)]
  var='x'
 else:
  py=[F,mir(Q),mir(pin),H,mir(H)]
  var='k'
 print(tag,'shape',[p.degrees() for p in py],flush=True)
 guard=cv(scale(G*mir(G))) if var=='x' else G
 out[tag]={'basis':[[[*map(int,e),int(c)] for e,c in p.terms()] for p in py],
           'guard':[[*map(int,e),int(c)] for e,c in guard.terms()],'var':var}
OUT=out

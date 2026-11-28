#!/usr/bin/env python3
"""Exact support when the all-active paired graph has exactly one zero third."""
import sympy as S
from math import gcd
v=S.Symbol('v')
Q=4*v**3-12*v*v+3*v+2
K=lambda w:1+2*w-w*w
H=lambda w:-2+w+4*w*w-w**3
def chart(mode,u,w,L,rr):
 if mode=='S':
  den=S.Integer(1);qg=K(u)
 else:
  den=H(u)
  qg=K(2*u)*den+4*u*u*(3*u-2)
 a={S.Integer(0):den,S.expand(u):K(u)*den,S.expand(w):qg}
 d=S.expand(L)
 r=a[S.expand(rr)]-K(v)*a[d]
 Y=4*v-L;D=L+2
 G=35*Y**4-30*Y**2*D**2+3*D**4
 return r,G
def support(a,b):
 n=[abs(int(S.resultant(Q,S.Poly(t,v),v).as_numer_denom()[0])) for t in (a,b)]
 val=gcd(*n)
 for p in (2,3,5,7):
  while val and val%p==0:val//=p
 return val
# gamma = 1/2, two second physical clocks differ, and c9 is the other forward off-zero.
out=[]
for name,u,w in [('S',2+v,-v),('A',-v/2,-v)]:
 r,G=chart(name,u,w,S.Integer(0),w)
 out.append(('midpoint',name,*[support(r,G)]))
for name,lag,go in [('S1',v,0),('S2',v,0),('S1',(v+2)/2,1),('S2',(v+2)/2,1),
                    ('A1',v,0),('A1',-v,1),('A2',v,0),('A2',2*v,1)]:
 L=lag
 z=2-L if name[:1]=='S' else (2*L if name=='A1' else L/2)
 u,w=(L,z) if name[-1]=='1' else (z,L)
 rr=z if go else S.Integer(0)
 r,G=chart(name[0],u,w,L,rr)
 out.append(('non-midpoint',name,go,support(r,G)))
assert len(out)==10 and all(t[-1]==1 for t in out)
for tag in out:print(tag)

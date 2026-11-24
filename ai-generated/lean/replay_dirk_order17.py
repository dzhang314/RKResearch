#!/usr/bin/env python3
"""Read-only independent arithmetic replay; Python standard library only.
Run next to the release's RKCert/ directory (or pass the directory explicitly).
The native Lean modules independently establish every asserted rank callback.
"""
from pathlib import Path
from fractions import Fraction
from math import lcm,prod
import ast,re,sys
C=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).parent/'RKCert'
p=1009;scale=12252240
assert all(p%d for d in range(2,32)) and scale==lcm(*range(2,18))
def coefficients(t):
 return [6*t*(4*t-25),-6*(34*t*t-90*t-375),30*(18*t*t+77*t-450),-15*(38*t*t+715*t-750),15*(14*t*t+885*t+2625),-2625*(2*t+27),31500]
def conv(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
for t in range(4):
 a=Fraction(t,15);shape=[(12*a-5)/70,(5-18*a)/14,18*a/7,-(5+6*a)/4,1]
 assert [31500*x for x in conv(conv([-1,1],[-a,1]),shape)]==coefficients(t)
def val(P,x):
 v=0
 for c in reversed(P):v=(c+x*v)%p
 return v
def determinant(a):
 A=[list(map(lambda x:x%p,r)) for r in a];d=1
 for i in range(len(A)):
  j=next((j for j in range(i,len(A)) if A[j][i]),None)
  if j is None:return 0
  if i!=j:A[i],A[j]=A[j],A[i];d=-d
  d=d*A[i][i]%p
  for j in range(i+1,len(A)):
   q=A[j][i]*pow(A[i][i],-1,p)%p
   A[j]=[(x-q*y)%p for x,y in zip(A[j],A[i])]
 return d%p
assert [t for t in range(p) if (t*t-24*t+150)%p==0]==[135,898]
count=0
for t in [135,898]:
 data=(C/f'DirkSevenData{t}.lean').read_text()
 P={a:ast.literal_eval(b) for a,b in re.findall(r'^def ([fgab]) : List ℤ:=(\[[^\n]+\])',data,re.M)}
 f,g,h,j=(P[n] for n in 'fgab');assert len(f)==len(g)==31 and len(h)<=30 and len(j)<=30
 F,G=conv(f,h),conv(g,j);assert [(x+y)%p for x,y in zip(F,G)]==[1]+[0]*(len(F)-1)
 for k,name in enumerate('fg'):
  for block in range(4):
   s=(C/f'DirkSevenLK{t}{k}{block}.lean').read_text()
   matches=re.findall(r'theorem [fg]sample(\d+):[^\n]+\n  trans \((\d+):E\)\n  · exact check_ldl _ _ _ \(by decide\) (\[[^\]]+\]) (\[[^\]]+\]) (\[[^\]]+\])',s)
   assert len(matches)==min(8,31-8*block)
   for it,vt,ew,lw,dw in matches:
    u=int(it)+2;v=int(vt);e,l,d=map(ast.literal_eval,(ew,lw,dw));a=coefficients(t)
    assert e==[sum(scale//(n+i+2)*a[i]*pow(u,6-i,p) for i in range(7))%p for n in range(10)]
    L=[[int(i==j) if i<=j else l[i*(i-1)//2+j] for j in range(5)]for i in range(5)]
    M=[[e[k+i+j] for j in range(5)]for i in range(5)]
    assert M==[[sum(L[i][r]*d[r]*L[j][r] for r in range(5))%p for j in range(5)]for i in range(5)]
    assert determinant(M)==prod(d)%p==v==val(P[name],u);count+=1
 print(f'{t}: minors degree {len(f)-1}, {len(g)-1}, leading residues {f[-1]}, {g[-1]}; resultant nonzero by Bezout.')
assert count==124
print(f'{count} cleared 5x5 determinants verified on 31 distinct samples for 4 degree-30 polynomials; 2 polynomial Bezout identities verified coefficientwise.')

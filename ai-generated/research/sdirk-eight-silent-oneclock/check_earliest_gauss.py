"""Build exact ideal identities for the earliest active Gauss cubic gate."""
import sympy as S
from sympy.polys.rings import ring
from itertools import product
from pathlib import Path

R,t,g,x=ring("t g x",S.QQ)
v=[t,g,x]
L4=lambda X:70*X**4-140*X**3+90*X**2-20*X+1
f=[t*t-R.domain(1,2),L4(g)/70,L4(x)/70]
exps=list(product(range(2),range(4),range(4)))
def poly(m):return R.from_dict({m:R.domain.one})
def rem(F):
 a,r=F.div(f)
 return r
def cub(g,a,b,x):
 return (x**4/4-g*x**3-(g+a+b)*(x**3/3-g*x**2)
         +(g*a+g*b+a*b)*(x**2/2-g*x)-g*a*b*(x-g))
def exact_phase(star):
 a=g*(2+2*t);b=g*(2-2*t) if star else g*(3+4*t)
 F=cub(g,a,b,x)
 C=[rem(poly(E)*F) for E in exps]
 mat=S.Matrix([[C[j].get(E,R.domain.zero) for j in range(len(exps))] for E in exps])
 rhs=S.Matrix([int(E==(0,0,0)) for E in exps])
 sol=list(mat.inv(method='DM')*rhs)
 A=sum(poly(E)*R.domain.convert(co) for E,co in zip(exps,sol))
 assert rem(A*F)==1
 qs,rr=(A*F-1).div(f)
 assert not rr and A*F-1==sum(a*b for a,b in zip(qs,f))
 return A,[qs[0],qs[1]/70,qs[2]/70]

def lean(P):
 terms=[]
 for E,k in sorted(P.items(),reverse=True):
  if not k:continue
  pos=k>0;k=abs(k);A=[(str(y) if p==1 else f"{y}^{p}") for y,p in zip(v,E) if p]
  coef=str(k.numerator) if k.denominator==1 else f"({k.numerator}/{k.denominator})"
  if k!=1 or not A:A=[coef]+A
  term='*'.join(A)
  terms.append(('+' if pos else '-')+term)
 if not terms:return "0"
 s=''.join(terms)
 return s[1:] if s[0]=='+' else s

if __name__=='__main__':
 for star in (True,False):
  A,C=exact_phase(star)
  print(star,"verified inverse supports",len(A),[len(p) for p in C],flush=True)
  if len(__import__('sys').argv)>1:
   name='starGauss' if star else 'arithmeticGauss'
   pp='g*(2-2*t)' if star else 'g*(3+4*t)'
   print(f'''
theorem {name} {{K : Type*}} [Field K] [CharZero K] (t g x : K)
    (ht : t^2-1/2=0)
    (hg : gaussFour g=0) (hx : gaussFour x=0) :
    earlyGaussCubic g (g*(2+2*t)) ({pp}) x≠0 := by
  intro hz
  unfold gaussFour at hg hx
  unfold earlyGaussCubic at hz
  have h : (1 : K)=0 := by
    linear_combination ({lean(A)})*hz-({lean(C[0])})*ht-({lean(C[1])})*hg-({lean(C[2])})*hx
  norm_num at h
''')

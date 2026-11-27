"""Exact elimination of a polynomial cubic-defect profile."""
from itertools import product
import sympy as S
X,t=S.symbols("X t")
R=t*t-S.Rational(1,2)
g=S.Rational(1,2);g1=g*g/2
red=lambda f:S.rem(S.expand(f),R,t)
def inv(f):
 h=S.invert(red(f),R,t)
 assert red(h*f)==1
 return h
def matin(M):
 d=inv(M.det())
 return M.adjugate().applyfunc(lambda v:red(v*d))
def gcd(a,b):
 a,b=red(a),red(b)
 while b:
  B=S.Poly(b,X)
  k=inv(B.LC())
  while a and (m:=S.Poly(a,X).degree())>=B.degree():
   a=red(a-red(k*S.Poly(a,X).LC())*X**(m-B.degree())*b)
  a,b=b,a
 return red(a*inv(S.Poly(a,X).LC()))
def end(sign,star):
 u=1+2*sign*t; w=2-u if star else 2*u
 r=0 if star else 3*u/2-1
 return tuple(map(red,(g*(1+u),g*(1+w),g*g1*u,g*g1*(w-r))))
leg=[S.legendre(j,2*X-1) for j in (3,4,5)]
def lv(c):return [red(f.subs(X,c)) for f in leg]

for fs,bs,sg in product((True,False),(True,False),(1,-1)):
 a,b,h,k=end(1,fs)
 c,d,j,l=end(sg,bs)
 c,d=red(1-c),red(1-d)
 M=S.Matrix([lv(a),lv(b),[red(l*u-j*v) for u,v in zip(lv(c),lv(d))]])
 J=(matin(M)*S.Matrix([h,k,0])).applyfunc(red)
 p=red(sum(a*b for a,b in zip(J,leg)))
 order=S.Poly(p,X).degree()
 assert order==5
 lead=inv(S.Poly(p,X).LC())
 moments=[1/S.Integer(i+1) for i in range(8)]
 def mean(f):
  return red(sum(v*moments[k] for (k,),v in S.Poly(f,X).terms()))
 for obj in (p*X**3,p*X**4,p*p,X*p*p):
  obj=red(obj)
  P=S.Poly(obj,X)
  r=len(moments)
  assert P.degree()==r
  moments.append(red(-mean(obj-P.LC()*X**r)*inv(P.LC())))
 S0=S.Matrix([[1,1,1],[g,a,b],[g*g-S.Rational(2,3)*g1,a*a,b*b]])
 ts=(matin(S0)*S.Matrix([X-g,X*X/2-g*X,X**3/3-g*X*X])).applyfunc(red)
 F=red(g1*ts[0]-p)
 P4=red((X-a)*(X-b)*(X-c)*(X-d))
 for n in (7,8):
  r=n-4
  M=S.Matrix(r,r,lambda i,j:mean(P4*X**(i+j)))
  cs=(matin(M)*S.Matrix([-mean(P4*X**(r+j)) for j in range(r)])).applyfunc(red)
  T=red(X**r+sum(v*X**k for k,v in enumerate(cs)))
  extra=mean(P4*T*X**3)
  assert gcd(F,T)==1
  inv(F.subs(X,c))
  inv(F.subs(X,d))
  if n==7: inv(extra)
  print(fs,bs,sg,n,"excluded",flush=True)

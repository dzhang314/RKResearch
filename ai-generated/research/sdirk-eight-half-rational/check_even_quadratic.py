"""Exact two-pole even profile filter for the half-diagonal endpoint pair."""
import sympy as S
from itertools import product
X,t=S.symbols('X t')
R=t*t-S.Rational(1,2)
g=S.Rational(1,2);g1=g*g/2
red=lambda f:S.rem(S.expand(f),R,t)
L=lambda x:70*x**4-140*x**3+90*x*x-20*x+1
I=lambda f:red(sum(c/S.Integer(k+1) for (k,),c in S.Poly(f,X).terms()))
def inv(f):
 a=S.invert(red(f),R,t);assert red(a*f)==1;return a
def matinv(A):
 d=inv(A.det())
 return A.adjugate().applyfunc(lambda a:red(d*a))
def gcd(a,b):
 a,b=red(a),red(b)
 while b:
  B=S.Poly(b,X);e=inv(B.LC())
  while a and (m:=S.Poly(a,X).degree())>=B.degree():
   a=red(a-red(e*S.Poly(a,X).LC())*X**(m-B.degree())*b)
  a,b=b,a
 return red(a*inv(S.Poly(a,X).LC()))
def endpoint(e,st):
 u=1+2*e*t;w=2-u if st else 2*u
 r=0 if st else 3*u/2-1
 return tuple(map(red,(g*(1+u),g*(1+w),g*g1*u,g*g1*(w-r))))
def qr(f,d):
 a,b=S.div(red(f),d,X)
 a,b=red(a),red(b)
 assert red(f-a*d-b)==0
 return a,b
for fs in (True,False):
 a,b,h,k=endpoint(1,fs)
 uv=(matinv(S.Matrix([[h,-L(a)],[k,-L(b)]]))*S.Matrix([-h*(a-g)**2,-k*(b-g)**2])).applyfunc(red)
 q=red((X-g)**2+uv[0]);p=red(uv[1]*L(X))
 print("front",fs,"q",q,"p factor",uv[1],flush=True)
 assert uv[1] and gcd(p,q)==1
 D=red(q*q)
 forms=(p*q,X*p*q,p*p,X*p*p)
 vectors=[qr(f,D) for f in forms]
 mat=S.Matrix([[S.Poly(v,X).nth(j) for j in range(4)] for u,v in vectors])
 omega=(matinv(mat)*S.Matrix([-I(u) for u,v in vectors])).applyfunc(red)
 def L2(f):
  h,r=qr(f,D)
  assert S.degree(h,X)<=7
  return red(I(h)+sum(omega[j]*S.Poly(r,X).nth(j) for j in range(4)))
 tapM=S.Matrix([[1,1,1],[g,a,b],[g*g-S.Rational(2,3)*g1,a*a,b*b]])
 tap=(matinv(tapM)*S.Matrix([X-g,X*X/2-g*X,X**3/3-g*X*X])).applyfunc(red)
 G=red(q*g1*tap[0]-p)
 for rs,e in product((True,False),(1,-1)):
  c,d,j,k0=endpoint(e,rs);c,d=red(1-c),red(1-d)
  if red(j*p.subs(X,d)*q.subs(X,c)-k0*p.subs(X,c)*q.subs(X,d)):
   print("  rear ratio excludes",rs,e,flush=True);continue
  P=red((X-a)*(X-b)*(X-c)*(X-d))
  inv(G.subs(X,c))
  inv(G.subs(X,d))
  print("  matching rear phase",rs,e,flush=True)
  for n in (7,8):
   k=n-4
   M=S.Matrix(k,k,lambda i,j:L2(P*X**(i+j)))
   d0=red(M.det())
   if not d0:
    print("  singular",n,flush=True);continue
   cs=(matinv(M)*S.Matrix([-L2(P*X**(k+j)) for j in range(k)])).applyfunc(red)
   Qn=red(X**k+sum(cs[j]*X**j for j in range(k)))
   extra=red(L2(P*Qn*X**3))
   assert gcd(G,Qn)==1
   if n==7: inv(extra)
   print("  n",n,"excluded",flush=True)

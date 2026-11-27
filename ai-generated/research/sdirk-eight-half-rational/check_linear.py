"""Central simple pole exclusion and a nonsingular benchmark for finiteness."""
from itertools import product
import sympy as S
X,t=S.symbols("X t")
R=t*t-S.Rational(1,2)
g=S.Rational(1,2);g1=g*g/2
red=lambda f:S.rem(S.expand(f),R,t)
def inv(f):
 v=S.invert(red(f),R,t);assert red(f*v)==1;return v
def matinv(M):
 d=inv(M.det())
 return M.adjugate().applyfunc(lambda a:red(d*a))
def gcd(a,b):
 a,b=red(a),red(b)
 while b:
  B=S.Poly(b,X);k=inv(B.LC())
  while a and (m:=S.Poly(a,X).degree())>=B.degree():
   a=red(a-red(k*S.Poly(a,X).LC())*X**(m-B.degree())*b)
  a,b=b,a
 return red(a*inv(S.Poly(a,X).LC()))
def end(sign,star):
 u=1+2*sign*t;w=2-u if star else 2*u;r=0 if star else 3*u/2-1
 return tuple(map(red,(g*(1+u),g*(1+w),g*g1*u,g*g1*(w-r))))
leg=[S.legendre(j,2*X-1) for j in (3,4,5)]
def lv(c):return [red(p.subs(X,c)) for p in leg]
def check(xi):
 q=X-xi
 for fs,bs,sg in product((True,False),(True,False),(1,-1)):
  a,b,h,k=end(1,fs)
  c,d,j,l=end(sg,bs);c,d=red(1-c),red(1-d)
  M=S.Matrix([lv(a),lv(b),[red(l*(d-xi)*v-j*(c-xi)*w) for v,w in zip(lv(c),lv(d))]])
  C=(matinv(M)*S.Matrix([h*(a-xi),k*(b-xi),0])).applyfunc(red)
  p=red(sum(i*j for i,j in zip(C,leg)))
  assert S.Poly(p,X).degree()==5
  P,s=S.div(p,q,X);P,s=red(P),red(s)
  if not s:
   assert xi==g
   print(fs,bs,sg,"central phase non-coprime",flush=True);continue
  assert S.degree(s,X)==0
  moments=[1/S.Integer(i+1) for i in range(8)]
  def I(f):
   return red(sum(v*moments[i] for (i,),v in S.Poly(f,X).terms()))
  L1=red(-I(P)*inv(s))
  def L(f):
   qq,rr=S.div(red(f),q,X)
   return red(I(qq)+rr*L1)
  def add(f,cor):
   F=S.Poly(red(f),X)
   assert F.degree()==len(moments)
   moments.append(red(-(I(F.as_expr()-F.LC()*X**F.degree())+cor)*inv(F.LC())))
  add(X**3*p,0)
  L2=red(-(I(P*P)+2*s*L(P))*inv(s*s))
  add(X*P*P,2*s*L(X*P)+s*s*(L1+xi*L2))
  def J(f):
   u,v=S.div(red(f),q*q,X)
   return red(I(u)+S.Poly(v,X).nth(0)*L2+S.Poly(v,X).nth(1)*(L1+xi*L2))
  M=S.Matrix([[1,1,1],[g,a,b],[g*g-S.Rational(2,3)*g1,a*a,b*b]])
  z=(matinv(M)*S.Matrix([X-g,X*X/2-g*X,X**3/3-g*X*X])).applyfunc(red)
  F=red(q*g1*z[0]-p)
  P4=red((X-a)*(X-b)*(X-c)*(X-d))
  for n in (7,8):
   k=n-4
   H=S.Matrix(k,k,lambda i,j:J(P4*X**(i+j)))
   inv(H.det())
   v=(matinv(H)*S.Matrix([-J(P4*X**(k+j)) for j in range(k)])).applyfunc(red)
   Q=red(X**k+sum(w*X**j for j,w in enumerate(v)))
   extra=J(P4*Q*X**3)
   assert S.degree(F,X)==5
   assert gcd(F,Q)==1
   inv(F.subs(X,c))
   inv(F.subs(X,d))
   if n==7: inv(extra)
   print(fs,bs,sg,n,"nonzero eliminants at",xi,flush=True)

if __name__=="__main__":
 check(S.Rational(1,2))
 check(S.Rational(1,3))

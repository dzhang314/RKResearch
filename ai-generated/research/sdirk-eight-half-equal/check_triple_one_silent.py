from itertools import product
import sympy as S
X,s,t = S.symbols('X s t')
Q=t*t-S.Rational(1,2)
gamma=S.Rational(1,2)
g1=gamma*gamma/2
L=lambda x:70*x**4-140*x**3+90*x*x-20*x+1
red=lambda p:S.rem(S.expand(p),Q,t)
def tinv(f):
 r=S.invert(red(f),Q,t);assert red(r*f)==1
 return r
def det(M):return red(S.det(M))
def inv(M):
 d=tinv(det(M));return M.adjugate().applyfunc(lambda p:red(p*d))
def gcd(f,g):
 f,g=red(f),red(g)
 while g:
  p=S.Poly(g,s);l=tinv(p.LC())
  while f and (m:=S.Poly(f,s).degree())>=p.degree():
   f=red(f-s**(m-p.degree())*red(S.Poly(f,s).LC()*l)*g)
  f,g=g,f
 return red(f*tinv(S.Poly(f,s).LC()))
def I(f):return red(sum(c/S.Integer(j+1) for (j,),c in S.Poly(f,X).terms()))
def divided(f,xi):
 f=red(f);q,r=S.div(f,X-xi,X);assert red(r-f.subs(X,xi))==0
 return red(q)
for fstar in (True,False):
 u=1+2*t;w=2-u if fstar else 2*u
 r=0 if fstar else 3*u/2-1
 a,b=red(gamma*(1+u)),red(gamma*(1+w))
 ha,hb=red(gamma*g1*u),red(gamma*g1*(w-r))
 M=S.Matrix([[1,1,1],[gamma,a,b],[gamma**2-S.Rational(2,3)*g1,a*a,b*b]])
 taps=(inv(M)*S.Matrix([s-gamma,s*s/2-gamma*s,s**3/3-gamma*s*s])).applyfunc(red)
 h=red(g1*taps[0])
 for eps,bstar,(f,hf) in product((1,-1),(True,False),((a,ha),(b,hb))):
  u0=1+2*eps*t
  v=2-u0 if bstar else 2*u0
  b1=red(1-gamma*(1+u0));b2=red(1-gamma*(1+v))
  xi=1-(S.Rational(21,74) if bstar else (59273*u0+42183)/S.Integer(112798))
  beta=red((f-xi)*hf*tinv(L(f)))
  assert beta!=0 # quadratic field inverses
  F=red((s-xi)*h-beta*L(s))
  P=(X-f)*(X-b1)*(X-b2)*(X-s)
  lp=I(divided(L(X),xi))
  lpv=red(L(xi))
  gates=[P*X**j for j in range(3)]
  data=S.Matrix([[I(p) for p in gates],[I(X*p) for p in gates],
                 [red(lp*p.subs(X,xi)-lpv*I(divided(p,xi))) for p in gates]])
  H=det(data)
  assert gcd(F,H)==1
  print(fstar,eps,bstar,f,'gcd 1',flush=True)

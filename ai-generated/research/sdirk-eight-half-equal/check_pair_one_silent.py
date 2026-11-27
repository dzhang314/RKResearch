from itertools import product
import sympy as S
t,s,y=S.symbols('t s y')
Q=t*t-S.Rational(1,2); gam=S.Rational(1,2);g1=gam*gam/2;lam=S.Rational(2,3)
L=lambda v:70*v**4-140*v**3+90*v*v-20*v+1
red=lambda F:S.rem(S.expand(F),Q,t)
def ti(F):
 h=S.invert(red(F),Q,t);assert red(F*h)==1;return h
def mi(A):
 return A.adjugate().applyfunc(lambda x:red(x*ti(A.det())))
class Fiber:
 def __init__(self,f):
  self.f=f
 def red(self,F):
  return red(S.rem(red(F),self.f,s))
 def inv(self,F):
  U,V=self.f,self.red(F)
  a,b=S.Integer(0),S.Integer(1)
  while V:
   v=S.Poly(V,s);i=ti(v.LC());q=0
   while U and (m:=S.Poly(U,s).degree())>=v.degree():
    h=red(S.Poly(U,s).LC()*i)*s**(m-v.degree())
    q+=h
    U=red(U-h*V)
   U,V=V,U
   a,b=b,self.red(a-q*b)
  if not U or S.degree(U,s): raise ValueError(U)
  w=self.red(a*ti(U));assert self.red(w*F)==1;return w
 def gcd(self,F,G):
  F,G=self.red(F),self.red(G)
  while G:
   h=S.Poly(G,y);i=self.inv(h.LC())
   while F and (m:=S.Poly(F,y).degree())>=h.degree():
    F=self.red(F-y**(m-h.degree())*self.red(S.Poly(F,y).LC()*i)*G)
   F,G=G,F
  if not F:return F
  return self.red(F*self.inv(S.Poly(F,y).LC()))
for st in (True,False):
 u=1+2*t;w=2-u if st else 2*u;r=0 if st else 3*u/2-1
 a,b=map(red,(gam*(1+u),gam*(1+w)))
 a1,b1,b2=map(red,(gam*u,gam*(w-r),gam*r))
 ha,hb=map(red,(g1*a1,g1*b1))
 A=S.Matrix([[1,1,1],[gam,a,b],[gam**2-lam*g1,a*a,b*b]])
 taps=(mi(A)*S.Matrix([s-gam,s*s/2-gam*s,s**3/3-gam*s*s])).applyfunc(red)
 hs=red(g1*taps[0])
 tau=lambda x,ts,cs:red(gam*x**3+sum(tap*c**3 for tap,c in zip(ts,cs))-x**4/4)
 Ah=(gam*ha,red(b2*ha+gam*hb),red(taps[1]*ha+taps[2]*hb+gam*hs))
 T=(tau(a,[a1],[gam]),tau(b,[b1,b2],[gam,a]),tau(s,taps,[gam,a,b]))
 for backstar,e,j in product((True,False),(1,-1),(0,1)):
  v=1+2*e*t
  xi=red(1-(S.Rational(21,74) if backstar else (59273*v+42183)/S.Integer(112798)))
  f,hf=(a,ha) if j==0 else (b,hb)
  beta=red((f-xi)*hf*ti(L(f)))
  ti(S.resultant(hs,L(s),s))
  F=red((s-xi)*hs-beta*L(s))
  for rt in (a,b,xi):
   while S.degree(F,s)>0 and not red(F.subs(s,rt)):
    F,rem=S.div(F,s-rt,s)
    assert not red(rem)
    F=red(F)
  if S.degree(F,s)==0:
   print(st,backstar,e,j,'no s');continue
  F=red(F*ti(S.Poly(F,s).LC()))
  fib=Fiber(F)
  # No pole/root of L at s. Know D!=0 by twin exclusion geometrically,
  # but checking its invertibility in the whole fiber permits Euclid.
  assert beta
  ti(L(xi))
  for k in (s-a,s-b,s-xi,L(s),s-f): fib.inv(k)
  den=red((a-b)*(a-s)*(b-s))
  d=(y-xi)
  hy=red(beta*L(y))
  t1=red(hy/g1)
  # All entries here are numerators in the common denominator y-xi.
  mu=[red(d*(y-gam)-t1),red(d*(y*y/2-gam*y)-gam*t1),
      red(d*(y**3/3-gam*y*y)+lam*hy-gam**2*t1)]
  def tap(n,m):return red(mu[2]-(n+m)*mu[1]+n*m*mu[0])
  ma=red((b-s)*tap(b,s));mb=red(-(a-s)*tap(a,s));ms=red((a-b)*tap(a,b))
  ay=red(gam*hy*den+ma*ha+mb*hb+ms*hs)
  ty=red((d*(gam*y**3-y**4/4)+t1*gam**3)*den+ma*a**3+mb*b**3+ms*s**3)
  gs=[]
  for fs,ys in ((Ah,ay),(T,ty)):
   D=fib.red(det:=S.Matrix([[hf,L(f),fs[j]],[hs,L(s),fs[2]],
                       [hy*den,L(y)*d*den,ys]]).det())
   for q in (f,s,xi):
    while S.degree(D,y)>0 and not fib.red(D.subs(y,q)):
     D,rr=S.div(D,y-q,y);assert not fib.red(rr)
     D=fib.red(D)
   gs.append(D)
  assert fib.gcd(*gs)==1
  print(st,backstar,e,j,'gcd 1',flush=True)

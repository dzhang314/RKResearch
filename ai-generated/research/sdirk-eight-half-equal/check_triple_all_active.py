import sympy as S
s,t=S.symbols('s t')
Q=t*t-S.Rational(1,2);g=S.Rational(1,2);g1=g*g/2;lam=S.Rational(2,3)
L=lambda x:70*x**4-140*x**3+90*x*x-20*x+1
red=lambda f:S.rem(S.expand(f),Q,t)
def tinv(f):
 i=S.invert(red(f),Q,t);assert red(i*f)==1
 return i
def gcd(f,h):
 f,h=red(f),red(h)
 while h:
  hh=S.Poly(h,s);i=tinv(hh.LC())
  while f and (m:=S.Poly(f,s).degree())>=hh.degree():
   f=red(f-s**(m-hh.degree())*red(S.Poly(f,s).LC()*i)*h)
  f,h=h,f
 if not f:return f
 return red(f*tinv(S.Poly(f,s).LC()))
for st in (True,False):
 u=1+2*t;w=2-u if st else 2*u;r=0 if st else 3*u/2-1
 a,b=red(g*(1+u)),red(g*(1+w))
 a1,b1,b2=map(red,(g*u,g*(w-r),g*r))
 ha,hb=red(g1*a1),red(g1*b1)
 M=S.Matrix([[1,1,1],[g,a,b],[g*g-lam*g1,a*a,b*b]])
 Mi=M.adjugate().applyfunc(lambda k:red(k*tinv(M.det())))
 q=(Mi*S.Matrix([s-g,s*s/2-g*s,s**3/3-g*s*s])).applyfunc(red)
 hs=red(g1*q[0])
 arows=(g*ha,red(g*hb+b2*ha),red(g*hs+q[1]*ha+q[2]*hb))
 tau=lambda c,ts,xs:red(g*c**3+sum(tap*y**3 for tap,y in zip(ts,xs))-c**4/4)
 trows=(tau(a,[a1],[g]),tau(b,[b1,b2],[g,a]),tau(s,q,[g,a,b]))
 mu=(-1/g1,-g/g1,lam-g*g/g1)
 def lagweight(x,y):
  return red(mu[2]-(x+y)*mu[1]+x*y*mu[0])
 den=red((a-b)*(a-s)*(b-s))
 ma=red(lagweight(b,s)*(b-s))
 mb=red(-lagweight(a,s)*(a-s))
 ms=red(lagweight(a,b)*(a-b))
 d=(den,ma,mb,ms)
 aff_A=red(g*den+ma*ha+mb*hb+ms*hs)
 aff_T=red((g**3/g1)*den+ma*a**3+mb*b**3+ms*s**3)
 assert red(ma+mb+ms-mu[0]*den)==0
 assert red(ma*a+mb*b+ms*s-mu[1]*den)==0
 assert red(ma*a*a+mb*b*b+ms*s*s-mu[2]*den)==0
 def gate(fs,fmid):
  return red(S.Matrix([[ha,a*ha,L(a),fs[0]],[hb,b*hb,L(b),fs[1]],[hs,s*hs,L(s),fs[2]],[den,den*g,0,fmid]]).det())
 F,G=gate(arows,aff_A),gate(trows,aff_T)
 assert gcd(F,G)==red((s-a)**2*(s-b)**2)
 print('star',st,'only repeated roots',flush=True)

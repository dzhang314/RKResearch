from itertools import product
import sympy as S
X,x,s,t = S.symbols("X x s t")
Q=t*t-S.Rational(1,2)
gamma=S.Rational(1,2)
g1=gamma*gamma/2
L=lambda y:70*y**4-140*y**3+90*y*y-20*y+1
red=lambda f:S.rem(S.expand(f),Q,t)
def tinv(q):
 u=S.invert(red(q),Q,t)
 assert red(u*q)==1
 return u
def det(M):
 return red(M.det())
def inv(M):
 d=tinv(det(M))
 return M.adjugate().applyfunc(lambda F:red(d*F))
def moments(p,j):
 return red(sum(k/S.Integer(i+j+1) for (i,),k in S.Poly(p,X).terms()))
class Fiber:
 def __init__(self,P):
  self.P=P
 def red(self,F):
  return red(S.rem(red(F),self.P,x))
 def inv(self,F):  # Euclid in Q[t]/(Q)[x] modulo P
  af,bf=self.P,self.red(F)
  a0,b0=S.Integer(0),S.Integer(1)
  while bf:
   b=S.Poly(bf,x); ilc=tinv(b.LC())
   q=S.Integer(0)
   while af and (m:=S.Poly(af,x).degree()) >= b.degree():
    c=red(S.Poly(af,x).LC()*ilc)*x**(m-b.degree())
    q+=c
    af=red(af-c*bf)
   af,bf=bf,af
   a0,b0=b0,self.red(a0-q*b0)
  if S.degree(af,x): raise ValueError(af)
  ai=self.red(a0*tinv(af))
  assert self.red(ai*F)==1
  return ai
 def gcd(self,F,G):
  F,G=self.red(F),self.red(G)
  while G:
   gg=S.Poly(G,s)
   ii=self.inv(gg.LC())
   while F and (m:=S.Poly(F,s).degree()) >= gg.degree():
    f=S.Poly(F,s)
    c=self.red(f.LC()*ii)*s**(m-gg.degree())
    F=self.red(F-c*G)
   F,G=G,F
  if not F:return F
  return self.red(F*self.inv(S.Poly(F,s).LC()))

for sf,star in product((1,), (True,False)):
 u=1+2*sf*t; w=2-u if star else 2*u; r=0 if star else 3*u/2-1
 a,b=red(gamma*(1+u)),red(gamma*(1+w))
 tr_a,tr_b,tr_c=map(red,(gamma*u,gamma*(w-r),gamma*r))
 ha,hb=red(g1*tr_a),red(g1*tr_b)
 lam=S.Rational(2,3)
 M=S.Matrix([[1,1,1],[gamma,a,b],[gamma**2-lam*g1,a*a,b*b]])
 t4=(inv(M)*S.Matrix([s-gamma,s*s/2-gamma*s,s**3/3-gamma*s*s])).applyfunc(red)
 hs=red(g1*t4[0])
 tau=lambda aa,st,chs:red(sum(k*z**3 for k,z in zip(st,chs))+gamma*aa**3-aa**4/4)
 f1=(gamma*ha,red(tr_c*ha+gamma*hb),red(t4[1]*ha+t4[2]*hb+gamma*hs))
 f2=(tau(a,[tr_a],[gamma]),tau(b,[tr_b,tr_c],[gamma,a]),tau(s,t4,[gamma,a,b]))
 # At active row5, strict taps to a,b,s have three clean moments.
 m1=lambda z:x**(z+1)/(z+1)-gamma*x**z
 d1=(a-b)*(a-s);d2=(b-a)*(b-s);d3=(s-a)*(s-b)
 n1=m1(2)-(b+s)*m1(1)+b*s*m1(0)
 n2=m1(2)-(a+s)*m1(1)+a*s*m1(0)
 n3=m1(2)-(a+b)*m1(1)+a*b*m1(0)
 den=red((a-b)*(a-s)*(b-s))
 f1x=red(ha*n1*(b-s)-hb*n2*(a-s)+hs*n3*(a-b))
 # Cubic evaluation of taps can be evaluated by nodal reduction.
 f2x=red(((a+b+s)*m1(2)-(a*b+a*s+b*s)*m1(1)+a*b*s*m1(0)+gamma*x**3-x**4/4)*den)
 def gate(fs,fx):
  A=S.Matrix([[ha,a*ha,L(a),fs[0]],[hb,b*hb,L(b),fs[1]],[hs,s*hs,L(s),fs[2]],[0,0,L(x)*den,fx]])
  return det(A)
 fg=[gate(f1,f1x),gate(f2,f2x)]
 # Remove known distinctness factors, only after exact division.
 gates=[]
 for F in fg:
  for v in (a,b):
   while S.degree(F,s)>0 and red(F.subs(s,v))==0:
    F,rr=S.div(F,s-v,s)
    assert not red(rr)
    F=red(F)
  gates.append(F)
 print('front',star,'degrees', [S.Poly(F,s,x).degree_list() for F in gates],flush=True)
 for sb,bstar in product((1,-1),(True,False)):
  y1=1+sb*t; y2=1-sb*t if bstar else S.Rational(3,2)+2*sb*t
  P=(X-1+y1)*(X-1+y2)
  H=S.Matrix(3,3,lambda i,j:moments(P,i+j))
  q=(inv(H)*S.Matrix([-moments(P,j) for j in range(3,6)])).applyfunc(red)
  mon=red(x**3+q[2]*x*x+q[1]*x+q[0])
  fib=Fiber(mon)
  print('  back',sb,bstar,'Q3',mon,flush=True)
  assert fib.gcd(*gates)==1
  print("   gcd 1",flush=True)

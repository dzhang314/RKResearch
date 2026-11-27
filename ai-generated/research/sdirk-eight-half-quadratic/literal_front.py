"""Exact degree-two literal row-five gate."""
from itertools import permutations
import sympy as S
from sympy.polys.rings import ring
K=S.QQ.algebraic_field(S.sqrt(2)/2)
R,s,Y,H=ring('s,Y,H',K)
T,t=K.unit,K.unit
g=K.convert(S.Rational(1,2))
g1=g*g/2
la=K.convert(S.Rational(2,3))
def det(M):
 out=0
 for p in permutations(range(len(M))):
  w=1
  for i,j in enumerate(p):
   w*=M[i][j]
   if not w:break
  if sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))%2:out-=w
  else:out+=w
 return out
def cramer(M,v):
 return [det([[v[i] if j==k else o for j,o in enumerate(r)] for i,r in enumerate(M)]) for k in range(len(M))]
def end(sign,front):
 u=1+2*sign*t;w=2-u if front else 2*u;r=K.zero if front else 3*u/2-1
 return g*(1+u),g*(1+w),g*g1*u,g*g1*(w-r),g*r
def L4(x):return 70*x**4-140*x**3+90*x*x-20*x+1
def factor_over_s(f):
 import sympy.polys.rings as rr
 J,x=rr.ring('x',K)
 P=J.from_dict({(i,):v for (i,j,k),v in f.items() if j==k==0})
 assert P.degree()==f.degree(s) and not f.degree(Y) and not f.degree(H)
 return [(U.as_expr(),n) for U,n in P.factor_list()[1]]
def front_data(front,info=False):
 a,b,ha,hb,u32=end(1,front)
 U=[[K.one,K.one,K.one],[g,a,b],[g*g-la*g1,a*a,b*b]]
 dU=det(U)
 ms=[s-g,s*s/2-g*s,s**3/3-g*s*s]
 ts=[T/dU for T in cramer(U,ms)]
 hs=g1*ts[0]
 ah=[g*ha,u32*ha+g*hb,ts[1]*ha+ts[2]*hb+g*hs]
 def tau(x,T,V):return g*x**3+sum(w*c**3 for w,c in zip(T,V))-x**4/4
 theta=[tau(a,[ha/g1],[g]),tau(b,[hb/g1,u32],[g,a]),tau(s,ts,[g,a,b])]
 M=[[ha,a*ha,L4(a)],[hb,b*hb,L4(b)],[hs,s*hs,L4(s)]]
 d=det(M)
 V=(a-b)*(a-s)*(b-s)
 h1=H/g1
 ms=[Y-g-h1,Y*Y/2-g*Y-g*h1,Y**3/3-g*Y*Y+la*H-g*g*h1]
 def tap(b,c):return ms[2]-(b+c)*ms[1]+b*c*ms[0]
 ma=(b-s)*tap(b,s);mb=(s-a)*tap(a,s);mss=(a-b)*tap(a,b)
 AH=g*H*V+ma*ha+mb*hb+mss*hs
 TH=(g*Y**3+h1*g**3-Y**4/4)*V+ma*a**3+mb*b**3+mss*s**3
 out=[]
 guard=(s-a)**2*(s-b)**2
 for e,Z in ((ah,AH),(theta,TH)):
  J=[r+[v] for r,v in zip(M,e)]
  ans=det(J+[[V*H,V*Y*H,V*L4(Y),Z]]).exquo(guard)
  A=ans.evaluate(H,K.zero)
  A=R.from_dict({(*k,0):v for k,v in A.items()})
  B=(ans-A).exquo(H)
  assert not B.degree(H)
  out.append((A,B))
 (A,B),(C,D)=out
 W=(A*D-B*C).exquo((Y-a)*(Y-b)*(Y-s))
 assert W.degree(Y)==2
 if info:
  print('front',front,'d',factor_over_s(d),flush=True)
  print('gate',S.factor(W.as_expr(),extension=S.sqrt(2)),flush=True)
  print('A B C D degree (s,y)',[(u.degree(s),u.degree(Y)) for u in (A,B,C,D)],flush=True)
 return a,b,ha,hb,hs,d,W,A,B,C,D,M
if __name__=='__main__':
 for k in (True,False):front_data(k,True)

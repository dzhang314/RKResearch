"""Equal invisible residuals, supported reverse degree-two row, detected h."""
from variable_atlas import K,t,S,z,H,J,Z,solve,ps
from itertools import product

L4=lambda x:70*x**4-140*x**3+90*x*x-20*x+1
I=lambda p:sum(v/(j+1) for (j,),v in p.items())
def ends(star,e):
 u=1+2*e*t;w=2-u if star else 2*u;r=K.zero if star else 3*u/2-1
 return 1+u,1+w,r
def h4(star):
 a,b,_=ends(star,1)
 T=[[1,1,1],[K.one,a,b],[2*K.one/3,a*a,b*b]]
 ss=solve(T,[z-1,z*z/2-z,z**3/3-z*z])
 return ps(ss[0])/2
def det3(m):return m[0]*m[2]*m[4]+2*m[1]*m[2]*m[3]-m[0]*m[3]**2-m[1]**2*m[4]-m[2]**3

def run():
 for f,j,r,s in product((True,False),(0,1),(True,False),(1,-1)):
  g=K.one/(1+ends(f,1)[j]);x=1-g
  assert L4(g)
  a,b,_=ends(r,s);c,d=1-g*a,1-g*b
  H=h4(f).compose(Z,Z/g)
  assert all(H.evaluate(Z,v) for v in (x,c,d))
  P=(Z-c)*(Z-d)
  # Two at the terminal cancel. Row four is a new scalar peg with zero defect.
  M=[I(P*Z**(i+1))-Z*I(P*Z**i) for i in range(5)]
  assert H.gcd(det3(M)).degree()==0
  # Three at the terminal, so it is itself an ordinary site.
  P*=Z-x
  M=[I(P*Z**j) for j in range(5)]
  if det3(M):continue
  A,B,C,D,_=M
  hh=A*C-B*B
  assert hh
  Q=Z*Z+((B*C-A*D)/hh)*Z+(B*D-C*C)/hh
  assert H.gcd(Q).degree()==0
  print("singular five-site factor checked by row-four cubic",f,j,r,s)
 print('full equal detected r2=0 phase census passed')
if __name__=='__main__':run()

"""Four active Gaussian rows, four distinct actual silent prefix clocks."""
from unequal_finite import Bfield,Epoly,JJ,Lco
from equal_detected import h4,ends
from itertools import product,permutations,combinations
from flint import nmod_poly
from sympy import isprime

def configs(p,t):
 P=lambda cs:nmod_poly(cs,p)
 B0=Bfield(P([0,1]),p,t)
 cv=lambda f: int(B0.cast(Epoly(JJ(f)))[0]) if f else 0
 M=P(list(Lco))
 roots=sorted(int(q) for q,e in M.roots() if e==1)
 assert len(roots)==4
 for st,g in product((True,False),roots):
  A,B,mid=ends(st,1)
  a,b,tap,ha,hb=map(cv,(A,B,mid,(A-1)/2,(B-1-mid)/2))
  h4p=B0.cast(Epoly(h4(st)))
  yield roots,st,g,a,b,tap,ha,hb,h4p

def act(p,g,A,B,mid,ha,hb,H4,r0,s0):
 I=lambda v:pow(int(v)%p,-1,p)
 q=lambda a,b:a*I(b)%p
 P=lambda ls:nmod_poly(ls,p)
 E=lambda f,x: int(f(int(x)%p))
 r,s=r0*I(g)%p,s0*I(g)%p
 L3=P([-1,12,-30,20])
 rho=q(E(L3,s0),E(L3,r0))
 def L(y,j):return (q(y**(j+1),j+1)-y**j)%p
 def LR(y,F):return sum(int(F[j])*L(y,j) for j in range(F.degree()+1))%p
 def det(M):
  from itertools import permutations
  return sum((-1)**sum(pi[i]>pi[j] for i in range(len(M)) for j in range(i+1,len(M))) *
             product_i(M[i][pi[i]] for i in range(len(M))) for pi in permutations(range(len(M))))%p
 def solve(M,b):
  d=I(det(M))
  return [det([[b[i] if j==k else w for j,w in enumerate(row)] for i,row in enumerate(M)])*d%p for k in range(len(M))]
 H=P(solve([[A**j for j in range(4)],[B**j for j in range(4)],[L(r,j) for j in range(4)],
            [L(s,j+1)-r*L(s,j)-rho*(L(r,j+1)-r*L(r,j)) for j in range(4)]],
           [ha,hb,0,0]))
 hr=E(H,r);q2=LR(s,H)
 assert hr
 lam=q(q2,hr)
 def K(F):return (LR(s,F)-rho*LR(r,F)-lam*E(F,r))%p
 hz,rem=divmod(H4-H,P([-A,1])*P([-B,1]))
 assert not rem
 assert hz.degree()==1
 z=q(-int(hz[0]),int(hz[1]))
 a2=P([-A,1])*P([-B,1])*P([-z,1])
 denom=K(a2)
 num=K(a2*P([0,1]))
 assert denom
 v=q(num,denom)
 # Actual row 4 and 5, with their unique literal strict feed.
 zH=E(H,z);vH=E(H,v)
 ztap=2*zH%p
 za=q(B*(z-1-ztap)-(z*z*I(2)-z-ztap),B-A)
 zb=(z-1-ztap-za)%p
 assert z not in (A,B)
 pred=[A,B,z]
 data=[(v-1-2*vH)%p,(v*v*I(2)-v-2*vH)%p,(v**3*I(3)-v*v-4*vH*I(3))%p]
 vt=solve([[n**j for n in pred] for j in range(3)],data)
 T=lambda c,w,ns:(c**3-c**4*I(4)+sum(w0*n**3 for w0,n in zip(w,ns)))%p
 Y=[
    [ha,A*ha,ha,T(A,[A-1],[1]),L4(p,g*A)],
    [hb,B*hb,hb+mid*ha,T(B,[B-1-mid,mid],[1,A]),L4(p,g*B)],
    [zH,z*zH,zH+za*ha+zb*hb,T(z,[ztap,za,zb],[1,A,B]),L4(p,g*z)],
    [vH,v*vH,vH+sum(x*h for x,h in zip(vt,[ha,hb,zH])),T(v,vt+[2*vH],pred+[1]),L4(p,g*v)]
 ]
 ranks=[det([[w[i] for i in ix] for w in Y]) for ix in combinations(range(5),4)]
 assert any(ranks)
 return True
def product_i(xs):
 y=1
 for x in xs:y*=x
 return y
def L4(p,x):return (70*x**4-140*x**3+90*x*x-20*x+1)%p

def main():
 p,t=1129,926
 assert isprime(p) and (2*t*t-1)%p==0
 count=0
 for roots,st,g,a,b,tap,ha,hb,h4p in configs(p,t):
  assert roots==[100,214,916,1030]
  x=(1-g)%p;assert x in roots
  for r,s in permutations([d for d in roots if d!=x],2):
   assert act(p,g,a,b,tap,ha,hb,h4p,r,s)
   count+=1
 assert count==48
 print('four active, all distinct prefix clocks excluded: 48 orientations',flush=True)
if __name__=='__main__':main()

"""Seven distinct active clocks, both literal fronts active, k!=0, Gauss hole."""
from one_front_zero import *
from variable_gamma import Lf,G
from both_front_silent8 import tail_projection

def exact_factors(front):
 A,B,m=ends(front,1);ha,hb=(A-1)/2,(B-1-m)/2
 LA,LB=Lf(G*A),Lf(G*B)
 q0=G*(B*hb*LA-A*ha*LB);q1=ha*LB-hb*LA
 L=sum(K.convert(q)*(-q0)**j*q1**(4-j) for j,q in enumerate(Lco))
 forb=G*q1*LA*LB
 while True:
  d=L.gcd(forb)
  if d.degree()==0:break
  L=L.exquo(d)
 Z=[q.monic() for q,e in L.factor_list()[1]]
 print('hole with both fronts exact diagonal factors',front,[q.degree() for q in Z],flush=True)
 return Z

def special(front,M,rear,hit,p,t):
 F,g,X,R,A,B,m,ha,hb,L,Q,P,H4=model(front,M)
 assert (A-R) and (B-R) and (X-R)
 us,k,c,d,H,q3,A9,B9,A8,B8=tail_poly(F,X,R,P,True if rear is None else rear)
 gap=X-R
 if hit==8:gap=2-gap if rear else gap/2
 k=ev(k,gap)
 if rear is None:
  E=[2*gap+k*(gap-2)]
 elif hit==9:E=[ev(add(B8,sc(A8,-R)),gap)]
 else:E=[ev(add(B9,sc(A9,-R)),gap),ev(q3,gap)]
 assert all(E)
 for U,j in reduced(M,p,t,[-gap,F(1)]):
  for e in E:U(e).inv()
 return True

def standard(front,M,rear,p,t):
 F,g,X,R,A,B,m,ha,hb,L,Q,P,H4=model(front,M)
 Y=tail_projection(front,M,False) if rear is None else projection(front,M,rear)
 if len(Y)<=1:return True
 ds=(g,X,R,A,B,m,ha,hb,P,H4)
 for U,u in reduced(M,p,t,Y):
  g,X,R,A,B,m,ha,hb=map(U,ds[:8]);P,H4=[list(map(U,T)) for T in ds[8:]]
  r=R*g;c=X-u;d=X-(2-u if rear else 2*u)
  pp=Pcoeff(U,r);nu=intp(U,pp)/ev(pp,r)
  pegs=[A,B,X,c]+([] if rear is None else [d])
  D=nodal([g*z for z in pegs]);dr=ev(D,r)
  mm=[intp(U,D,j)-dr*nu*r**j for j in range(4 if rear is None else 3)]
  if rear is not None:
   a,b,c=mm;(a*c-b*b).inv();continue
  a,b,c,d=mm;h=a*c-b*b;h.inv()
  Y=[(b*d-c*c)/(h*g*g),(b*c-a*d)/(h*g),U(1)]
  E=first5(U,A,B,m,ha,hb,P,H4)
  V=first5(U,A,B,m,ha,hb,[],H4)
  multicol(Y,E).inv();ev(V,R).inv()
 return True

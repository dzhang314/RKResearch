"""Complete undetected six-active equal-tag chart: fixed monic degree-(3,3,4,2,2) replay."""
from equal_five import *
def check(front):
 for ar,m in h4(front).monic().factor_list()[1]:
  F=ExField(Epoly(ar.monic()));s=F(E(P([0,1])))
  cv=lambda x:F(Epoly(JJ(x))) if x else F(0)
  a,b,r=map(cv,ends(front,1))
  ha,hb=(a-1)/2,(b-1-r)/2
  A=(b*(s-1)-(s*s/2-s))/(b-a);B=(s*s/2-s-a*(s-1))/(b-a)
  Ah=A*ha+B*hb;T4=s**3-s**4/4+A*a**3+B*b**3
  assert Ah
  nodes=[a,b,s]
  m=[[-F(1),F(1)],[F(0),-F(1),F(1)/2],[F(0),F(0),-F(1),F(1)/3]]
  weights=[]
  for i,v in enumerate(nodes):
   ns=[q for j,q in enumerate(nodes) if i!=j]
   den=(v-ns[0])*(v-ns[1])
   weights.append(sc(sum_poly([sc(t,w) for t,w in zip(m,nodal(ns))]),1/den))
  P4=add([F(0),F(0),F(0),F(1),-F(1)/4],sum_poly([sc(x,v**3) for x,v in zip(weights,nodes)]))
  AB=sum_poly([sc(weights[0],ha),sc(weights[1],hb)])
  X=add(sc(P4,Ah),sc(AB,-T4));assert not ev(X,s)
  Y0,err=divp(X,[-s,F(1)]);assert not err
  print(front,ar.degree(),len(Y0)-1,len(gcdp(X,AB))-1,[bool(ev(Y0,c)) for c in (a,b,s)],flush=True)
  assert len(gcdp(X,AB))==1
  assert all(ev(Y0,c) for c in (a,b,s))
  yield ar.monic(),F,(a,b,s,ha,hb,Ah,T4),monic_u(Y0),AB
def direct_units(front,p,t):
 for H,F,data,R,J0 in check(front):
  B0=Bfield(nmod_poly([0,1],p),p,t)
  Good=B0.cast(Epoly(H))
  assert Good.degree()==H.degree() and Good.leading_coefficient()==1
  for m,e in Good.factor()[1]:
   assert e==1
   B=Bfield(m,p,t)
   U=Tower([B(x) for x in R]);y=U.gen()
   a,b,s,ha,hb,Ah,T4=map(U,data)
   AhY=ev(list(map(U,J0)),y)
   L=lambda r:sum(U(v)*r**j for j,v in enumerate(Lco))
   Q=lambda g:Ah*L(g*y)-AhY*L(g*s)
   cand=[U(1)/2,1/(1+s),1/(1+y)]
   roots=[r for r in range(p) if sum(v*r**j for j,v in enumerate(Lco))%p==0]
   if len(roots)==4:cand.extend(map(U,roots))
   for i,g in enumerate(cand):
    try:Q(g).inv()
    except ArithmeticError:
     print('not a unit',front,p,t,m,i,flush=True);return False
 return True

def projection_data(front,p,t):
 for H,F,data,R,J0 in check(front):
  B0=Bfield(nmod_poly([0,1],p),p,t)
  Good=B0.cast(Epoly(H))
  assert Good.degree()==H.degree() and Good.leading_coefficient()==1
  for m,e in Good.factor()[1]:
   assert e==1
   B=Bfield(m,p,t)
   U=Tower([B(x) for x in R]);y=U.gen()
   a,b,s,ha,hb,Ah,T4=map(U,data)
   AhY=ev(list(map(U,J0)),y)
   Q=[U(v)*(Ah*y**j-AhY*s**j) for j,v in enumerate(Lco)]
   assert len(Q)==5
   yield U,a,b,s,y,ha,hb,Ah,AhY,T4,monic_u(Q)

def nd(ns):
 q=[[1]]
 for r in ns:
  z=[[] for j in range(len(q)+1)]
  for i,d in enumerate(q):
   z[i]=add(z[i],sc(mul(d,r),-1));z[i+1]=add(z[i+1],d)
  q=z
 return q
def pdet(M):
 a,b,c,d,e=M
 return sum_poly([mul(mul(a,c),e),sc(mul(mul(b,c),d),2),sc(mul(a,mul(d,d)),-1),sc(mul(mul(b,b),e),-1),sc(mul(mul(c,c),c),-1)])
def five_output(front,p,t):
 for U,a,b,s,y,ha,hb,Ah,AhY,T4,Q in projection_data(front,p,t):
  H=nd([[U(0),s],[U(0),y],[U(1),-U(1)]])
  M=[sum_poly([sc(d,U(1)/(i+j+1)) for i,d in enumerate(H)]) for j in range(5)]
  D=pdet(M)
  try:
   u=gcdp(D,Q)
   assert len(u)==1
  except ArithmeticError:
   return False
 return True

class Nested(Tower):
 def __call__(self,x):
  if isinstance(x,V) and x.A is self:return x
  return V(qr(x if isinstance(x,list) else [self.B(x)],self.F)[1],self)

def sums(qs):return sum_poly(qs)
def matrix_num(H,j,y):
 return det([[y[i] if l==j else h for l,h in enumerate(U)] for i,U in enumerate(H)])
def lagrange(ns):
 out=[]
 for i,v in enumerate(ns):
  others=[c for j,c in enumerate(ns) if i!=j]
  d=prod_i([v-c for c in others])
  out.append(sc(nodal(others),d.inv()))
 return out
def prod_i(xs):
 out=1
 for x in xs:out*=x
 return out
def graph(inputs,g,alpha,beta):
 U=g.A
 L=[U(v)*g**j for j,v in enumerate(Lco)]
 m=[]
 for j in range(4):
  q=[U(0)]*j+[-U(1),U(1)/(j+1)]
  m.append(add(q,sc(L,beta)) if j==3 else q)
 return m,L

def verify_six(front,p,t,verbose=False):
 for U,a,b,s,y,ha,hb,Ah,AhY,T4,Q in projection_data(front,p,t):
  G=Nested(Q);g=G.gen()
  a,b,s,y,ha,hb,Ah,AhY,T4=map(G,(a,b,s,y,ha,hb,Ah,AhY,T4))
  bfront=[a,b,s,y];x=1-g
  g.inv()
  baseL=[G(v)*g**j for j,v in enumerate(Lco)]
  Ls=ev(baseL,s);alpha,beta=Ah/Ls,T4/Ls
  raw,L=graph(bfront,g,alpha,beta)
  cards=lagrange(bfront)
  w=[sums([sc(m,c) for m,c in zip(raw,v)]) for v in cards]
  AhPart=sums([sc(w[0],ha),sc(w[1],hb)])
  P0=add(AhPart,sc(L,-alpha))
  Zcoef,rem=qr(P0,nodal([s,y]));assert not rem and len(Zcoef)==3
  W=Nested(monic_u(Zcoef));z=W.gen();gv=W(g)
  a,b,s,y,ha,hb,Ah,AhY,T4,x,alpha,beta=map(W,(a,b,s,y,ha,hb,Ah,AhY,T4,x,alpha,beta))
  w=[[W(c) for c in d] for d in w];cards=[[W(c) for c in d] for d in cards]
  L=list(map(W,L));bfront=list(map(W,bfront));AhPart=list(map(W,AhPart))
  for v in (s,y): (z-v).inv()
  (gv*z-x).inv()
  pegs=[gv*s,gv*y,gv*z,x]
  P4=nodal(pegs)
  M=[sum(W(v)/(i+j+1) for i,v in enumerate(P4)) for j in range(4)]
  A,B,C,D=M;h=A*C-B*B
  Qm=[(B*D-C*C)/h,(B*C-A*D)/h*gv,gv*gv]
  N=Nested(monic_u(Qm));u=N.gen();ln=lambda d:[N(c) for c in d]
  # Each active grade-five pure column belongs to span L3,L4,c L4.
  # First three strictly chronological values determine all three coefficients.
  basis=lambda v:[20*(gv*v)**3-30*(gv*v)**2+12*(gv*v)-1,ev(L,v),v*ev(L,v)]
  H=[basis(v) for v in (s,y,z)]
  d=det(H).inv()
  # Fourth row adds the predecessor at z. Its one remaining coefficient
  # follows from actual grade-four A h, without using a global B inverse.
  R=[ev(c,z) for c in cards]
  dif=-(ha*R[0]+hb*R[1])
  uL=ev(ln(L),u)
  T=(N(alpha)*uL-ev(ln(AhPart),u))/N(dif)
  w4=[ev(ln(q),u)-T*N(r) for q,r in zip(w,R)]+[T]
  def gradefive(v,mom,node):
   return v**4-v**5/5+sum(z*x**4 for z,x in zip(mom,node))
  V0=[gradefive(v,[ev(u,v) for u in w],bfront) for v in (s,y,z)]
  coeff=[matrix_num(H,j,V0)*d for j in range(3)]
  val=gradefive(u,w4,list(map(N,bfront+[z])))
  su=[20*(N(gv)*u)**3-30*(N(gv)*u)**2+12*(N(gv)*u)-1,uL,u*uL]
  gate=val-sum(N(c)*r for c,r in zip(coeff,su))
  gate.inv()
  print('six distinct excluded using actual grade-five clock-power read',front,flush=True)
 return True

def main():
 p,t=1129,203
 assert SY.isprime(p) and (2*t*t-1)%p==0
 for f in (True,False):
  assert direct_units(f,p,t)
  assert five_output(f,p,t)
  assert verify_six(f,p,t)
if __name__=='__main__':main()

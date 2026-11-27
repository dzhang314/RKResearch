"""Five-active support with silent third-last row: exact saturated degree-(3,9) fibers."""
from equal_six import *

def monic_u(f):return sc(f,f[-1].inv())
def sr(f,P,strip=True):
 while True:
  d=gcdp(f,P)
  if len(d)<2:return f
  f,r=divp(f,d);assert not r
  if not strip:return monic_u(f)

def consts(front,t0):
 H=h4(front).monic()
 A,C,_=ends(front,1);B,_,_=ends(True,t0)
 P3=(X-Y*Z0)*(X-(1-Y))*(X-(1-Y*B))
 M=[avg(P3,j) for j in range(5)]
 Pr=trip(M);hh=M[0]*M[2]-M[1]**2
 for ar,_ in H.factor_list()[1]:
  FF=ExField(Epoly(ar.monic()));s=FF(E(P([0,1])))
  cv=lambda x:FF(Epoly(JJ(x)))
  a,b=map(cv,(A,C))
  ha=(a-1)/2;hb=(b-1-(0 if front else 3*(a-1)/2-1))/2
  def cast(f):
   F=[FF(0)]*(1+max(j for _,j in f))
   for (i,j),v in f.items():F[j]+=cv(v)*s**i
   return trim(F)
  R=cast(Pr);D=cast(hh)
  # At the actual witness all three pegs are distinct, gamma !=0,
  # and the two missing ordinary sites make D !=0.
  assert R and D
  G=mul(mul([FF(0),FF(1)],D),mul([-FF(1),1+s],[-FF(1),cv(B)+s]))
  raw=len(R)-1
  R=sr(R,G)
  R=sr(R,deriv(R),False)
  print('H4,H3 raw->guarded degrees',front,t0,ar.degree(),raw,len(R)-1,flush=True)
  assert len(R)==10 and ar.degree()==3
  yield ar.monic(),monic_u(R),(a,b,s,ha,hb,cv(B))

def check(H,G,data,pp,tt):
 B0=Bfield(nmod_poly([0,1],pp),pp,tt)
 Mh=B0.cast(Epoly(H))
 assert Mh.degree()==H.degree() and Mh.leading_coefficient()==1
 for f,n in Mh.factor()[1]:
  B=Bfield(f,pp,tt)
  U=Tower([B(x) for x in G]);g=U.gen()
  a,b,s,ha,hb,A=data
  a,b,s,ha,hb,A=map(U,(a,b,s,ha,hb,A))
  c,x=1-g*A,1-g
  assert (s*g-x).inv() and (s*g-c).inv() and (c-x).inv() and g.inv()
  P3=nodal([x,c,s*g]);Ja=lambda h:sum(U(w)/(k+1) for k,w in enumerate(h))
  M=[Ja([0]*k+P3) for k in range(5)]
  assert trip(M)==0
  M0,M1,M2,M3,_=M
  hh=M0*M2-M1*M1
  xy=[(M1*M3-M2*M2)/hh,(M1*M2-M0*M3)/hh,U(1)]
  Ta=(b*(s-1)-(s*s/2-s))/(b-a);Tb=(s*s/2-s-a*(s-1))/(b-a)
  assert (Ta*ha+Tb*hb).inv()
  T4=s**3-s**4/4+Ta*a**3+Tb*b**3
  nodes=[a,b,s]
  mm=[[-U(1),U(1)],[U(0),-U(1),U(1)/2],[U(0),U(0),-U(1),U(1)/3]]
  weights=[]
  for i,v in enumerate(nodes):
   ns=[q for j,q in enumerate(nodes) if i!=j]
   den=(v-ns[0])*(v-ns[1])
   weights.append(sc(sum_poly([sc(t,w) for t,w in zip(mm,nodal(ns))]),1/den))
  tau=add([U(0),U(0),U(0),U(1),-U(1)/4],sum_poly([sc(x,v**3) for x,v in zip(weights,nodes)]))
  L0=[U(i)*g**j for j,i in enumerate(Lco)]
  V=add(sc(tau,ev(L0,s)),sc(L0,-T4))
  Q=[xy[i]*g**i for i in range(3)]
  assert len(gcdp(V,Q))==1
def main():
 p,t=1009,285
 assert SY.isprime(p) and (2*t*t-1)%p==0
 for front,rear in product((True,False),(1,-1)):
  for H,G,model in consts(front,rear):
   check(H,G,model,p,t)
   print('silent eighth equal five-active unit check',front,rear,H.degree(),p,t,flush=True)
if __name__=='__main__':main()

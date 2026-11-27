"""Equal invisible tags with supported w, undetected h, six active zeros."""
from unequal_finite import *
from equal_detected import ends,h4,det3 as trip
R3,X,Z0,Y=ring('X z g',K)
RZ,z0,g0=ring('z g',K)
def avg(poly,j=0):
 return RZ.from_dict({(i,k):sum(v/(d+j+1) for (d,s,t),v in poly.items() if s==i and t==k)
                      for _,i,k in poly.keys()})
def outerp(poly):
 return RZ.from_dict({(j,0):k for (j,),k in poly.items()})
def away(front,back,eps):
 H=h4(front).monic()
 A,B,_=ends(back,eps)
 R=(X-Y*Z0)*(X-(1-Y))*(X-(1-Y*A))*(X-(1-Y*B))
 m=[avg(R,j) for j in range(4)]
 f=m[0]*m[2]-m[1]**2
 g=m[0]*m[3]-m[1]*m[2]
 P=JJ(f.resultant(outerp(H)))
 Qp=JJ(g.resultant(outerp(H)))
 G0=P.gcd(Qp);d=G0.gcd(JJ.gens[0]**100)
 G0=G0.exquo(d)
 print('unfixed distinct x,s',front,back,eps,'unpruned degree',G0.degree(),flush=True)
 assert G0.degree()==0
 return G0

def visit(front,gamma_builder,xmode):
 h=h4(front).monic()
 for ar,m in h.factor_list()[1]:
  F=ExField(Epoly(ar.monic()));s=F(E(P([0,1])))
  cv=lambda x:F(Epoly(JJ(x)))
  a,b,_=ends(front,1)
  A,B,_,_,_,_,_,_,_,_=phases(front)
  ha,hb=(A-1)/2,(B-1-(K.zero if front else 3*(A-1)/2-1))/2
  a,b,ha,hb=map(cv,(a,b,ha,hb))
  Ta=(b*(s-1)-(s*s/2-s))/(b-a);Tb=(s*s/2-s-a*(s-1))/(b-a)
  assert Ta*ha+Tb*hb
  T4=s**3-s**4/4+Ta*a**3+Tb*b**3
  g=gamma_builder(F,s,cv)
  assert g
  for rear,ee in product((True,False),(1,-1)):
   C,D,_=ends(rear,ee)
   c,d,x=1-g*cv(C),1-g*cv(D),1-g
   P3=nodal([x,c,d])
   Ja=lambda p:sum(F(u)/(j+1) for j,u in enumerate(p))
   if xmode:
    assert s*g==x
    M=[Ja([0]*j+P3) for j in range(5)]
    assert trip(M)
    continue
   assert all(s*g!=t for t in (x,c,d))
   P4=nodal([x,c,d,s*g])
   V=[Ja([0]*j+P4) for j in range(4)]
   assert V[0]*V[2]-V[1]**2 or V[0]*V[3]-V[1]*V[2]
   # Six distinct ordinary sites and at most four pegged ones.
   M0,M1,M2,M3=V;hh=M0*M2-M1*M1
   if not hh:continue
   Q2=[(M1*M3-M2*M2)/hh,(M1*M2-M0*M3)/hh,F(1)]
   # Next active row y has only strict-feed clocks a,b,s for its scalar moments.
   nodes=[a,b,s]
   mm=[[-F(1),F(1)],[F(0),-F(1),F(1)/2],[F(0),F(0),-F(1),F(1)/3]]
   weights=[]
   for i,v in enumerate(nodes):
    ns=[q for j,q in enumerate(nodes) if i!=j]
    den=(v-ns[0])*(v-ns[1])
    weights.append(sc(sum_poly([sc(t,w) for t,w in zip(mm,nodal(ns))]),1/den))
   tau=add([F(0),F(0),F(0),F(1),-F(1)/4],sum_poly([sc(x,v**3) for x,v in zip(weights,nodes)]))
   L0=[F(i)*g**j for j,i in enumerate(Lco)]
   V=add(sc(tau,ev(L0,s)),sc(L0,-T4))
   Qphysical=[Q2[i]*g**i for i in range(3)]
   assert len(gcdp(V,Qphysical))==1
 print("fixed x or s cases checked",front,xmode,flush=True)

if __name__=='__main__':
 for f,b,t0 in product((True,False),(True,False),(1,-1)):away(f,b,t0)
 for f in (True,False):
  visit(f,lambda F,s,cv:1/(1+s),True)
  for i in (0,1):
   a=ends(f,1)[i]
   visit(f,lambda F,s,cv:1/(1+cv(a)),False)

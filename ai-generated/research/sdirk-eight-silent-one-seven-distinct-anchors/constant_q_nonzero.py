"""Seven distinct, both literal fronts active, constant Q and k nonzero."""
from seven_k0_anchors import *
from variable_gamma import Lf,G as Gamma

@lru_cache(None)
def gamma_factors(front):
 A,B,m=ends(front,1);ha,hb=(A-1)/2,(B-1-m)/2
 D=(ha*Lf(Gamma*B)-hb*Lf(Gamma*A)).monic()
 return [q.monic() for q,e in D.factor_list()[1]]

@lru_cache(None)
def gap(front,M,rear,extra):
 F=ExField(Epoly(M));g=F(E(P([0,1])))
 A,B,m=map(lambda x:cv(F,x),ends(front,1))
 ha,hb=(A-1)/2,(B-1-m)/2
 L=list(map(F,Lco));q=ev(L,g*A)/ha;assert q and q==ev(L,g*B)/hb
 x=1-g;u=[F(0),F(1)];k=[F(1),F(2),F(-1)];c=[x,-g]
 d=[x-2*g,g] if rear else [x,-2*g]
 px=ev(L,x);pc=subst(L,c);pd=subst(L,d)
 ds=[g,A,B,m,ha,hb,q,x]
 if rear is None:
  assert extra
  T=add(mul([F(-2),F(1)],pc),sc(add(sc(u,2),mul(k,[F(-2),F(1)])),-px))
 elif not extra:T=add(pc,sc(k,-px))
 elif rear:T=sum_poly([mul([F(2),F(-1)],pc),sc(mul(u,pd),-1),sc(mul(k,[F(-2),F(2)]),px)])
 else:
  H=[F(-2),F(1),F(4),F(-1)];Q=[F(2),F(3),F(-12),F(4)]
  T=sum_poly([sc(mul(Q,pc),2),mul(H,pd),sc(mul(k,Q),-px)])
 guards=[u,k,pc]
 if rear is not None:guards.extend([add(d,sc(c,-1)),add(d,[-x]),pd])
 P0=mon(guarded(T,guards))
 print('constant-Q nonzero exact gap',front,M.degree(),rear,extra,len(P0)-1,flush=True)
 return P0,ds

def moment_const(F,pegs,jcount):
 L=list(map(F,Lco));D=mul(L,L);assert len(D)==9
 I=[F(1)/(j+1) for j in range(8)]
 a=-sum(D[j]*I[j] for j in range(8))/D[8]
 b=-(sum(D[j]*I[j+1] for j in range(7))+D[7]*a)/D[8]
 I.extend([a,b])
 M=nodal(pegs)
 return [sum(q*I[j+i] for i,q in enumerate(M)) for j in range(jcount)]

def test(front,M,rear,extra,p,t):
 U0,ds=gap(front,M,rear,extra)
 if len(U0)<=1:return True
 V=Bfield(nmod_poly([0,1],p),p,t)
 Md=V.cast(Epoly(M));assert Md.degree()==M.degree() and Md.leading_coefficient()==1
 for M0,_ in Md.factor()[1]:
  F=Bfield(M0,p,t)
  G=Tower(list(map(F,U0)));u=G.gen()
  g,A,B,m,ha,hb,q,x=map(G,ds)
  c=x-g*u;d=x-g*(2-u if rear else 2*u)
  pegs=[g*A,g*B,x,c]+([] if rear is None else [d])
  mm=moment_const(G,pegs,6 if rear is None else 5)
  if rear is not None:
   det3(mm).inv()
   continue
  H=[[mm[i+j] for j in range(3)] for i in range(3)]
  D=det(H);D.inv()
  Y=[v/(D*g**(3-i)) for i,v in enumerate(cramer(H,[-mm[3],-mm[4],-mm[5]]))]+[G(1)]
  C=[G(v)*g**i/q for i,v in enumerate(Lco)]
  H4=[cv(G,j) for j in pol(h4(front),lambda x:x)]
  multicol(Y,first5(G,A,B,m,ha,hb,C,H4)).inv()
 return True

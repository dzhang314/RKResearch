"""Physical eighth is the separate w site: four pegs, actual fifth and sixth."""
from five_peg_checks import *

def nodal_pol(q,b,K):
 Hn=newton(K,7)
 Cs=[can(q*q),can(2*q*b),can(b*b)]
 V=bezout()
 C=[can(sum(Cs[i]*(expr(V[i][j]) if j<len(V[i]) else 0) for i in range(3))) for j in range(4)]
 A=[]
 for i in range(5):
  R=[can(sum(Lco[s]*Hn[i][s+j-i] for s in range(5) if s+j>=i)) for j in range(4)]
  R.append(can(sum(C[j]*Hn[i][j-i] for j in range(i,4))))
  A.append(R)
 return poly_det(A)

@lru_cache(None)
def polys_silent(front):
 A,B,m,ha,hb,H4,qA,qB,q0,q1,sh,e,QT,QA,DT,DA=phases(front)
 al,bl=map(expr,(A,B))
 qa,qb=term(q0,g),term(q1,g)
 x=1-g;c=x-g*u;k=1+2*u-u*u
 L4=lambda x:sum(v*x**i for i,v in enumerate(Lco))
 Qp=lambda x:g*qa+qb*x
 pA,pB=g*al,g*bl
 M=nodal_pol(g*qa,qb,[pA,pB,x,c,g*y])
 R=can((u-2)*L4(c)*Qp(x)-(2*u+k*(u-2))*L4(x)*Qp(c))
 R=exdiv(R,u)
 # Literal pure-four cross: eliminate the unknown fourth clock before h=P(y).
 M0=y-1;M1=y*y/2-y;M2=y**3/3-y*y
 J=M2-(al+bl)*M1+al*bl*M0
 T0=y**3-y**4/4+(al+bl)*M2-al*bl*M1
 A0=expr(sh[0])*M0+expr(sh[1])*M1+expr(e[0])*J
 LT=expr(DT[0])-term(QT,y);LA=expr(DA[0])-term(QA,y)
 E5=can((A0-expr(e[1])*T0)*(qa+qb*y)+(LA-expr(e[1])*LT)*L4(g*y))
 E5=exdiv(exdiv(E5,y-al),y-bl)
 print('silent extra raw polynomials',front,R.degrees(),E5.degrees(),M.degrees(),flush=True)
 return R,E5,M

@lru_cache(None)
def silent_projection(front):
 T,E5,H=polys_silent(front)
 R=can(E5.resultant(H,0))
 print('silent extra y projection',front,R.degrees(),flush=True)
 S=gcoeff(can(T.resultant(R,1)));assert S
 D=mon(guarded(S,physical_guard(front)))
 A=exact_uc(T);B=exact_uc(R)
 # Only the γ-leading coefficients are used for an exact retained branch split.
 tl=A[-1];z=A[0]
 xc={}
 for (i,j,k),v in parts(E5).items():
  if i==3 and not j:xc[k]=v
 yl=[xc.get(k,F2(0)) for k in range(max(xc)+1)]
 print('silent extra exact projection',front,len(S)-1,len(D)-1,
       'gap lead',len(gcdp(D,tl))-1,'y lead',len(gcdp(D,yl))-1,'u0',len(gcdp(D,z))-1,flush=True)
 return D,T,E5,H,R,tl,yl,z

def split_poly(M,gs):
 L=[(M,frozenset())]
 for name,G in gs:
  K=[]
  for dom,fs in L:
   A=gcdp(dom,G);B=mon(guarded(dom,[G]))
   if len(A)>1:K.append((A,fs|{name}))
   if len(B)>1:K.append((B,fs))
  L=K
 return L

def silent_fields(front,p,t):
 M,T,E5,H,R,tl,yl,z=silent_projection(front)
 for dom,flags in split_poly(M,[('u0',z),('ulead',tl),('ylead',yl)]):
  for U,gamma in base_finite(dom,p,t):
   coeff=coefficients(U,T,gamma,1)
   deg=3 if 'ulead' in flags else 4
   assert len(coeff)==deg+1,(flags,len(coeff))
   if 'u0' in flags:
    assert not coeff[0]
    coeff=coeff[1:]
   V=Tower(mon(coeff));vg=V(gamma);vu=V.gen()
   T0=coefficients(V,E5,vg,0)
   deg=2 if 'ylead' in flags else 3
   assert len(T0)==deg+1,(flags,len(T0))
   W=Nested(mon(T0));y0=W.gen();gg,uu=map(W,(vg,vu))
   h=evalg(W,H,gg)
   e=sum(a*y0**i*uu**j for (i,j),a in h.items())
   yield W,gg,uu,y0,e,flags

def marked_six(F,gamma,s5,hphase):
 A,B,m,ha,hb,H4,qA,qB,q0,q1,sh,e,QT,QA,DT,DA=[*hphase]
 A,B,m,ha,hb=map(F,(A,B,m,ha,hb));H4,q0,q1,sh,e,QT,QA=map(lambda v:list(map(F,v)),(H4,q0,q1,sh,e,QT,QA))
 Q0,Q1=[ev(v,gamma) for v in (q0,q1)]
 QP=[Q0,Q1];LP=[F(k)*gamma**i for i,k in enumerate(Lco)]
 q5,p5=ev(QP,s5),ev(LP,s5)
 def mom(t):
  Z=[[-F(1),F(1)],[F(0),-F(1),F(1)/2],[F(0),F(0),-F(1),F(1)/3],
     [F(0),F(0),F(0),-F(1),F(1)/4]]
  U=[add(mul(v,QP),sc(LP,k)) for v,k in zip(Z[:3],(-2,-2,-F(4)/3))]
  U.append(add(mul(Z[3],QP),mul(LP,add(QT,[F(-2)]))))
  return U
 M=mom(None)
 t0,t1,t2=[ev(a,s5) for a in M[:3]]
 J=t2-(A+B)*t1+A*B*t0
 # The literal τ4 read at row five: T0+Z4*J=0 in Q-cleared units.
 T0=(s5**3-s5**4/4)*q5+(2-ev(QT,s5))*p5+(A+B)*t2-A*B*t1
 def read(z4):
  H2=add(sh,sc(nodal([A,B]),ev(e,z4)))
  F3=nodal([A,B,z4])
  v0=add(mul(add(QA,[F(-1)]),LP),sc(sum_poly([sc(x,k) for x,k in zip(M,H2)]),-1))
  v1=sum_poly([sc(x,k) for x,k in zip(M,F3)])
  return add(sc(v0,q5*ev(F3,s5)),sc(v1,q5*ev(H2,s5)-p5))
 G0,Gp,Gm=[read(F(z)) for z in (0,1,-1)]
 G1=sc(add(Gp,sc(Gm,-1)),F(1)/2)
 G2=add(sc(add(Gp,Gm),F(1)/2),sc(G0,-1))
 G=sum_poly([sc(G0,J*J),sc(G1,-J*T0),sc(G2,T0*T0)])
 return G,(gphase(F,A,B,Q0,Q1),J,T0)

def gphase(F,A,B,a,b):return A,B,a,b

def verify_silent(front,p,t):
 phase=phases(front)
 for W,g,u,y,e,flags in silent_fields(front,p,t):
  K,(phase0,J,T0)=marked_six(W,g,y,phase)
  A,B,a,b=phase0
  x=1-g;c=x-g*u
  M=moment(W,[g*A,g*B,x,c,g*y],[g*a,b],4)
  m0,m1,m2,m3=M
  Y=[m1*m3-m2*m2,(m1*m2-m0*m3)*g,(m0*m2-m1*m1)*g*g]
  span_unit(W,e,scaled_quadratic_resultant(W,K,Y))
 return True

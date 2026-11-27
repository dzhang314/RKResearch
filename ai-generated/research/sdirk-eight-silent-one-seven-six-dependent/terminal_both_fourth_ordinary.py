"""Canceled terminal double, both literal fronts silent, fourth row ordinary."""
from one_front_zero import *
from equal_undetected_front import nd,pdet
from both_front_silent8 import context

def data(F,front,rear,sg,s):
 A,B,m=map(lambda p:F(Epoly(JJ(p))) if p else F(0),ends(front,1))
 a,b,_=map(lambda p:F(Epoly(JJ(p))) if p else F(0),ends(rear,sg))
 ha,hb=(A-1)/2,(B-1-m)/2
 H4=[F(Epoly(JJ(v))) if v else F(0) for v in pol(h4(front),lambda q:q)]
 return A,B,m,a,b,ha,hb,H4

@lru_cache(None)
def projection(front,rear,sg,H):
 F=ExField(Epoly(H))
 s=F(E(P([0,1])))
 A,B,m,a,b,ha,hb,H4=data(F,front,rear,sg,s)
 D=nd([[F(0),s],[F(1),-a],[F(1),-b]])
 P0=[sum_poly([sc(d,F(1)/(i+j+1)) for i,d in enumerate(D)]) for j in range(5)]
 G=pdet(P0)
 assert G
 guards=mul([F(0),F(1)],add(mul(P0[0],P0[2]),sc(mul(P0[1],P0[1]),-1)))
 g0=strip(G,guards)
 print('both fronts silent ordinary-four exact diagonal',front,rear,sg,H.degree(),len(g0)-1,flush=True)
 return F,s,g0,(A,B,m,a,b,ha,hb,H4)

def pure(F,A,B,m,ha,hb,H4,s):
 sh,AA,e,QT,QA=context(F,A,B,m,ha,hb,None,H4)
 U=F(1)
 th=[F(-1),U];H1=[F(0),-U,U/2];H2=[F(0),F(0),-U,U/3]
 J=sum_poly([H2,sc(H1,-A-B),sc(th,A*B)])
 T5=sum_poly([[F(0),F(0),F(0),U,-U/4],sc(H2,A+B),sc(H1,-A*B),sc(J,s)])
 A5=sum_poly([sc(th,sh[0]),sc(H1,sh[1]),sc(J,ev(e,s))])
 jH=-F(4)/3+2*(A+B)-2*A*B
 dt=2-F(4)/3*(A+B)+2*A*B+s*jH
 da=1-2*sh[0]-2*sh[1]+ev(e,s)*jH
 wa=(B*(s-1)-(s*s/2-s))/(B-A);wb=s-1-wa
 tr=s**3-s**4/4+wa*A**3+wb*B**3
 ar=wa*ha+wb*hb
 return T5,A5,dt,da,tr,ar,QT,QA

def verify(front,rear,sg,H,p,t):
 F,s0,g0,ds=projection(front,rear,sg,H)
 if len(g0)<=1:return True
 base=Bfield(nmod_poly([0,1],p),p,t)
 M=base.cast(Epoly(H));assert M.degree()==H.degree() and M.leading_coefficient()==1
 for M,_ in M.factor()[1]:
  U=Bfield(M,p,t);s=U(nmod_poly([0,1],p))
  W=Tower(list(map(U,g0)));g=W.gen();s=W(s)
  A,B,m,a,b,ha,hb=map(W,ds[:7]);H4=list(map(W,ds[7]))
  X=1/g-1;c=1-g*a;d=1-g*b
  D=nodal([g*s,c,d]);q=[intp(W,D,j) for j in range(4)];a0,a1,a2,a3=q
  hh=a0*a2-a1*a1
  Y=[(a1*a3-a2*a2)/(hh*g*g),(a1*a2-a0*a3)/(hh*g),W(1)]
  T5,A5,dt,da,tr,ar,QT,QA=pure(W,A,B,m,ha,hb,H4,s)
  L=[W(v)*g**i for i,v in enumerate(Lco)]
  rt,ra=tr/ev(L,s),ar/ev(L,s)
  t0=add(T5,sc(L,-rt));a0=add(A5,sc(L,-ra))
  LH=(ev(L,B)/hb-ev(L,A)/ha)/(B-A)
  LH=ev(L,A)/ha+(X-A)*LH
  t1=dt-(ev(QT,X)-rt*LH);a1=da-(ev(QA,X)-ra*LH)
  (ev(t0,X)*a1-ev(a0,X)*t1).inv()
  test_poly(Y,t0,a0)
 return True

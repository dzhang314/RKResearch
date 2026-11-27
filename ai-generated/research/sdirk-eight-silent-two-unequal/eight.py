"""Eight active zero rows: rank-three census or literal second-extra-zero read."""
from unequal_finite import *
import sys
from off8_fibers import multicol,cramer
def row6(front,g,a,b,s,ha,hb,hs,sg,Qf,t,p):
 U=g.A
 L=list(map(U,Lco))
 v=1+2*t;w=2-v if front else 2*v;r=0 if front else 3*v*pow(2,-1,p)-1
 TA=(g*a**3+g*v*g**3-a**4/4)/ha
 TB=(g*b**3+g*(w-r)*g**3+g*r*a**3-b**4/4)/hb
 sl=(TB-TA)/(b-a)
 T=[TA-a*sl,sl]
 if front:
  assert s==g
  C=nodal([g,a,b])
  G=add([U(0)]+[U(x)/(j+1) for j,x in enumerate(C)],sc(C,-g))
  K0=add(T,[-2*(g+a+b)/3])
  return add(mul(Qf,G),mul(K0,L))
 assert s!=g
 M=[]
 for i in range(4):
  f=[U(0)]*i+[-g,U(1)/(i+1)]
  M.append(mul(Qf,f))
 M[2]=add(M[2],sc(L,U(2)/3))
 M[3]=add(M[3],mul(T,L))
 nodes=[g,a,b,s]
 weights=[]
 for i,x in enumerate(nodes):
  ys=[z for j,z in enumerate(nodes) if i!=j]
  d=U(1)
  for y in ys:d*=x-y
  weights.append(sc(sum_poly([sc(m,co) for m,co in zip(M,nodal(ys))]),1/d))
 pSlope=g*r*ha/hb/(b-a)
 sigma=g*sg;g1=g*g/2
 R=mul([sigma+a*pSlope,-pSlope],L)
 for w,k in zip(weights,[-sigma*g1,ha,hb,hs]):R=add(R,sc(w,k))
 return R
def verify8(front,rear,data,p0,t0,exactn):
 assert rear is not None
 M,F,vals=data
 p=int(p0);t=int(t0)
 E0=Epoly(M)
 B0=Bfield(nmod_poly([0,1],p),p,t)
 Md=B0.cast(E0)
 assert Md.degree()==M.degree() and Md.leading_coefficient()==1
 for f,n in Md.factor()[1]:
  assert n==1
  B=Bfield(f,p,t);C=Tower([B(x) for x in F])
  g,a,b,s,ha,hb,hs,sg,x,Qf=vals
  g,a,b,s,ha,hb,hs,sg,x=map(C,(g,a,b,s,ha,hb,hs,sg,x));Qf=list(map(C,Qf))
  u=C.gen();c=x-g*u;d=x-g*(2-u if rear else 2*u)
  pegs=[a,b,s,c,d,x]
  if exactn==7:
   for ii in range(6):det3(moment(C,pegs[:ii]+pegs[ii+1:],Qf)).inv()
   continue
  W=moment(C,pegs,Qf,4)
  d=W[0]*W[2]-W[1]**2
  q=[(W[1]*W[3]-W[2]**2)/d,(W[1]*W[2]-W[0]*W[3])/d,C(1)]
  F6=row6(front,g,a,b,s,ha,hb,hs,sg,Qf,t,p)
  multicol(q,F6).inv()
 return True
def run():
 for front in (True,False):
  if len(sys.argv)>1 and int(sys.argv[1])!=int(front):continue
  m=exact_fifth(front)
  for rear in (True,False):
   w=exact_tail(front,rear,m)
   for n0 in (7,8):
    for p in SY.primerange(997,2200):
     p=int(p)
     for t in SY.sqrt_mod(pow(2,-1,p),p,all_roots=True):
      try:verify8(front,rear,w,p,t,n0)
      except (ArithmeticError,ValueError):continue
      print("closed eight-active",front,rear,n0,p,t,flush=True)
      break
     else:continue
     break
    else:print("no eight-active unit",front,rear,n0,flush=True)
if __name__=='__main__':run()

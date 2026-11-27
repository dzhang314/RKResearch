"""Finite exact one-repeat profile recheck at all scalar pivot fibers."""
from shared_profile_projection import *
from check_star_family import FE,Split
from check_arithmetic_family import SF,SplitT
from functools import lru_cache
from itertools import product

class SplitRoot(Exception):
 def __init__(self,ctx,ss):self.ctx,self.ss=ctx,ss
def nu(f):
 if not f:return False
 if isinstance(f,(int,Q)):return True
 if isinstance(f,FE):
  f.chk();return True
 assert isinstance(f,Ext)
 d=f.norm()
 if d:
  assert nu(d)
  return True
 assert f.b and nu(f.b)
 x=-f.a/f.b;y=-f.ctx.c1-x
 raise SplitRoot(f.ctx,[x] if x==y else [x,y])
def div(a,b):
 assert nu(b)
 return a/b
def value(f,x,y,K):
 return sum(K(w)*x**i*y**j for (i,j,k),w in f.items() if not k)

def profile_test(data,q,p,red):
 front,rear,sign,yp,ri,deg,pegs,he,k,l,h0,D,n,rv,front_data=data
 a,b,s,y,c,d=pegs;rr=pegs[ri]
 assert not ev(q,rr) and not ev(p,rr)
 for x in [u for i,u in enumerate(pegs+(n,)) if i!=ri]:
  if not nu(ev(q,x)):return "discordant pole"
 if nu(rear_ratio(q,p,c,d,k,l)):return "rear ratio"
 B=Bop(D,p)
 assert not B[-1]
 for z in cross(B,mul(q,red)):
  if nu(z):return "Bezout scalar"
 lam=B[len(mul(q,red))-1] # q and reduced q are monic here
 if not nu(lam):return "zero dual mass"
 p0,m=divmod_monic(p,[-rr,pegs[0].ctx(1) if isinstance(pegs[0],FE) else 1])
 assert not m
 if deg==2:
  xi=-red[0]
  if not nu(ev(p0,xi)):return "non-maximal shared factor"
 print("one-repeat scalar survivor",data[:6],flush=True)
 return None

def choose_solve(F0,y,Y0,key,vals):
 front,rear,sign,yp,ri,deg=key
 a,b,ha,hb,Hs,d,W,AA,BB,CC,DD,M=vals
 c,e,k,l,_=LF.end(sign,rear);c,e=1-c,1-e
 K=lambda f:F0(Rat.k(f).numerator())
 a,b,c,e,ha,hb,k,l=map(K,(a,b,c,e,ha,hb,k,l))
 s=F0(E(P([0,1])))
 pegs=(a,b,s,y,c,e)
 for i,x in enumerate(pegs):
  for j in range(i):
   if not nu(x-pegs[j]):return "clock collision"
 if not nu(value(d,s,y,K)):return "early rank"
 D,h0,h1=nodal6(pegs)
 if not nu(h0):return "six-peg integral"
 u=div(h1,h0)
 for x in pegs:
  if not nu(u-x):return "last clock duplicates"
 if not nu(value(BB,s,y,K)):
  den=value(DD,s,y,K)
  if not nu(den):
   assert nu(value(AA,s,y,K)) or nu(value(CC,s,y,K))
   return "no fifth affine read"
  h=-div(value(CC,s,y,K),den)
 else:h=-div(value(AA,s,y,K),value(BB,s,y,K))
 if nu(value(AA,s,y,K)+value(BB,s,y,K)*h) or nu(value(CC,s,y,K)+value(DD,s,y,K)*h):
  return "literal fifth read"
 H=(ha,hb,value(Hs,s,y,K),h)
 F0rows=[Rv(x) for x in pegs[:4]]
 a1=(0,1,2)
 dets=det([F0rows[j] for j in a1])
 if not nu(dets):
  a1=(0,1,3)
  dets=det([F0rows[j] for j in a1])
 assert nu(dets)
 j0=5-a1[-1]
 rx=pegs[ri]
 data=(front,rear,sign,yp,ri,deg,pegs,H,k,l,h0,D,u,rx,vals)
 def coeff(q):
  vv=cramer([F0rows[j] for j in a1],[H[j]*ev(q,pegs[j]) for j in a1])
  return [div(sum(vv[j]*(Lpoly[j][i] if i<len(Lpoly[j]) else 0) for j in range(3)),dets) for i in range(6)]
 qL=[-rx,F0(1)];pL=coeff(qL)
 el=ev(pL,pegs[j0])-H[j0]*ev(qL,pegs[j0])
 if deg==1:
  if nu(el):return "linear fourth value"
  return profile_test(data,qL,pL,[F0(1)])
 q0=[F0(0),-rx,F0(1)];q1=[rx,-F0(1),F0(0)]
 p0=coeff(q0);p1=sc(pL,-1)
 F00=ev(p0,pegs[j0])-H[j0]*ev(q0,pegs[j0])
 F11=-el
 def test(xi):
  q=add(q0,sc(q1,xi));p=add(p0,sc(p1,xi))
  return profile_test(data,q,p,[-xi,F0(1)])
 if nu(F11):return test(-div(F00,F11))
 if nu(F00):return "quadratic fourth value"
 R0=mul([ev(q0,e),ev(q1,e)],[ev(p0,c),ev(p1,c)])
 R1=mul([ev(q0,c),ev(q1,c)],[ev(p0,e),ev(p1,e)])
 Rr=add(sc(R0,l),sc(R1,-k));assert Rr
 if len(Rr)==1:return "constant rear ratio"
 if len(Rr)==2:return test(-div(Rr[0],Rr[1]))
 CC=Ring2(div(Rr[0],Rr[2]),div(Rr[1],Rr[2]))
 try:return test(CC.gen())
 except SplitRoot as e:
  if e.ctx is not CC:raise
  ans=[test(x) for x in e.ss]
  return None if None in ans else ans

@lru_cache(maxsize=2)
def reads(front):return LF.front_data(front)

def on_scalar(M,key,theta=None):
 F0=SF(M,theta)
 front,rear,sign,yp,ri,deg=key
 s=F0(E(P([0,1])))
 vals=reads(front);a,b,ha,hb,hs,d,W,*_=vals
 if front:
  y=3*s/2-F0(Q(1,4)) if yp==0 else F0(Q(103,72))-s
  return choose_solve(F0,y,None,key,vals)
 rv=W.exquo(d.exquo((LF.s-a)*(LF.s-b)))
 K=lambda c:F0(Rat.k(c).numerator())
 qy=trim([sum(K(v)*s**i for (i,j,k),v in rv.items() if j==d0 and not k) for d0 in range(3)])
 assert qy
 if len(qy)==1:return "no fifth clock"
 if len(qy)==2:return choose_solve(F0,-div(qy[0],qy[1]),None,key,vals)
 R=Ring2(div(qy[0],qy[2]),div(qy[1],qy[2]))
 try:return choose_solve(F0,R.gen(),R,key,vals)
 except SplitRoot as e:
  assert e.ctx is R
  ans=[choose_solve(F0,x,None,key,vals) for x in e.ss]
  return None if None in ans else ans

def check(M,key,theta=None):
 try:r=on_scalar(M,key,theta)
 except SplitT as e:
  assert theta is None
  return check(M,key,e.v) and check(M,key,-e.v)
 except Split as e:
  a=e.f
  assert 0<a.degree()<M.degree()
  return check(a,key) and check(M.exact(a),key)
 print('one-repeat finite factor',key,M.degree(),r,flush=True)
 return r is not None

from itertools import permutations

def six_clocks(front,rear,sgn):
 a,b,ha,hb,hs,d,W,*_=LF.front_data(front)
 R=W.exquo(d.exquo((LF.s-a)*(LF.s-b)))
 c,e,k,l,_=LF.end(sgn,rear);c,e=1-c,1-e
 a,b,c,e=map(Rat.k,(a,b,c,e))
 P4=node_factor((a,b,c,e))
 T=[I([0]*j+P4) for j in range(4)]
 H=[[T[0],T[1]],[T[1],T[2]]]
 hd=det(H)
 assert hd
 q0,q1=[u/hd for u in cramer(H,[-T[2],-T[3]])]
 M=Ring2(q0,q1)
 x=M.gen();v=-q1-x
 rest=[M(c),M(e),x,v]
 for s0,y0 in permutations(rest,2):
  g=evaluate(R,s0,y0)
  assert g.norm()

if __name__=="__main__":
 for f,r,e in product((True,False),(True,False),(1,-1)):
  if r and e==-1:continue
  six_clocks(f,r,e)
 print("excluded six physical clocks in all six relative phases",flush=True)
 found=0
 for key,M in charts():
  ksys=tuple(int(x) for x in sys.argv[1:])
  if ksys and tuple(map(int,key[:len(ksys)]))!=ksys:continue
  unit,fac=M.factor();back=P(unit)
  for p,e in fac:
   back*=p**e
   assert check(E(p/p.leading_coefficient()),key),key
  assert back==M
  found+=1
  print("excluded one-repeat chart",key,M.degree(),flush=True)
 if len(sys.argv)==1:assert found==72

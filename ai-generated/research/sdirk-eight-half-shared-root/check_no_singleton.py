"""Exact finite singleton-discrepancy atlas, without dividing at a physical pole."""
from pathlib import Path
import sys
research=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(research/name) for name in
              ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic")]
import literal_front as LF
import check_exceptional_fibers as FF
from check_star_family import *
from itertools import product

class YSplit(Exception):
 def __init__(self,ys):self.ys=ys
def guard(u):
 if not u:return False
 if isinstance(u,FE):
  u.chk();return True
 assert isinstance(u,Ext)
 n=u.norm()
 if n:
  assert guard(n)
  return True
 assert u.b and guard(u.b)
 y1=-u.a/u.b;y2=-u.ctx.c1-y1
 raise YSplit([y1] if y1==y2 else [y1,y2])
def div(a,b):
 assert guard(b)
 return a/b
def monic(x):
 return trim([div(v,x[-1]) for v in x])
def y_gcd(F1,F2):
 a,b=trim(F1),trim(F2)
 while b:a,b=b,divmod_monic(a,monic(b))[1]
 return monic(a) if a else []
def scalar_proj(front,Ssite):
 a,b,ha,hb,hs,d,W,A,B,C,D,M=LF.front_data(front)
 R=W.exquo(d.exquo((LF.s-a)*(LF.s-b)))
 dguard=FF.w(d)
 if Ssite:
  H=FF.w(hs)
 else:
  H=FF.Gcd(FF.res(R,A),FF.res(R,C))
 assert H
 H=FF.strip(H,dguard)
 val=[]
 for f,m in H.factor_list()[1]:
  f=f.monic()
  x=[Rat.k(f.get((i,),LF.K.zero)).numerator() for i in range(f.degree()+1)]
  y=E(P([w.a[0] for w in x]),P([w.b[0] for w in x]))
  assert y.degree()==f.degree()
  val.append(y)
 print('s projection',front,Ssite,H.degree(),[m.degree() for m in val],flush=True)
 return val

def addpoly(a,b):
 n=max(len(a),len(b));return trim([x+y for x,y in zip(a+[0]*(n-len(a)),b+[0]*(n-len(b)))])
def scale(a,v):return trim([x*v for x in a])
def chart(F0,front,Ssite,y,rear,sgn):
 a,b,ha,hb,hs,d,W,A,B,C,D,M=LF.front_data(front)
 c,e,k,l,_=LF.end(sgn,rear);c,e=1-c,1-e
 K=lambda x:F0(Rat.k(x).numerator())
 a,b,ha,hb,c,e,k,l=map(K,(a,b,ha,hb,c,e,k,l))
 s=F0(E(P([0,1])))
 def at(P0):return sum(K(w)*s**i*y**j for (i,j,z),w in P0.items() if not z)
 if any(not guard(v) for v in (s-a,s-b,y-a,y-b,y-s,at(d))):return []
 if Ssite:
  assert at(hs)==0
  u=at(B)
  if not u:
   u=at(D)
   if not u:return []
   hy=-div(at(C),u)
  else:hy=-div(at(A),u)
  if guard(at(A)+at(B)*hy) or guard(at(C)+at(D)*hy):return []
  r=s
 else:
  assert at(A)==0 and at(C)==0
  hy=F0(0);r=y
 if not guard(r-c) or not guard(r-e):return []
 h_s=at(hs)
 rows=[Rv(x) for x in (a,b,s,y)]
 vals=[ha,hb,h_s,hy]
 nodes=[a,b,s,y]
 ix=(0,1,2);de=det([rows[i] for i in ix])
 if not de:
  ix=(0,1,3);de=det([rows[i] for i in ix])
 assert guard(de)
 j=5-ix[-1]
 qlin=[-r,F0(1)]
 q0=[0,-r,F0(1)];q1=[r,-F0(1),0]
 def gen_poly(q):
  co=cramer([rows[i] for i in ix],[vals[i]*ev(q,nodes[i]) for i in ix])
  return [div(sum(co[l]*(Lpoly[l][k] if k<len(Lpoly[l]) else 0) for l in range(3)),de) for k in range(6)]
 pL=gen_poly(qlin)
 p0,p1=map(gen_poly,(q0,q1))
 U0=ev(p0,nodes[j])-vals[j]*ev(q0,nodes[j])
 U1=ev(p1,nodes[j])-vals[j]*ev(q1,nodes[j])
 def ratio(q,p):return l*ev(q,e)*ev(p,c)-k*ev(q,c)*ev(p,e)
 out=[]
 if not guard(ev(pL,nodes[j])-vals[j]*ev(qlin,nodes[j])) and not guard(ratio(qlin,pL)):
  out.append((qlin,pL))
 if U1:
  xi=-div(U0,U1)
  q,p=[x+xi*z for x,z in zip(q0,q1)], [x+xi*z for x,z in zip(p0,p1)]
  if not guard(ratio(q,p)):out.append((q,p))
 elif not guard(U0):
  R1=mul([ev(v,e) for v in (q0,q1)],[ev(v,c) for v in (p0,p1)])
  R2=mul([ev(v,c) for v in (q0,q1)],[ev(v,e) for v in (p0,p1)])
  rr=addpoly(scale(R1,l),scale(R2,-k))
  if not rr:
   # A whole line may only be an already inadmissible common rear pole.
   assert any(not ev(q0,u) and not ev(q1,u) for u in (c,e))
  elif len(rr)==2:
   xi=-div(rr[0],rr[1])
   out.append(([x+xi*z for x,z in zip(q0,q1)], [x+xi*z for x,z in zip(p0,p1)]))
  elif len(rr)==3:
   E2=Ring2(div(rr[0],rr[2]),div(rr[1],rr[2]))
   xi=E2.gen()
   out.append(([E2(x)+xi*z for x,z in zip(q0,q1)], [E2(x)+xi*z for x,z in zip(p0,p1)]))
 keep=[]
 for q,p in out:
  keep.append((q,p))
 return keep

def through_ys(F0,front,Ssite,case):
 a,b,ha,hb,hs,d,W,A,B,C,D,M=LF.front_data(front)
 R=W.exquo(d.exquo((LF.s-a)*(LF.s-b)))
 xi=F0(E(P([0,1])))
 K=lambda x:F0(Rat.k(x).numerator())
 def cv(U):
  return trim([sum(K(w)*xi**i for (i,j,z),w in U.items() if j==ell and not z) for ell in range(U.degree(LF.Y)+1)])
 yq=cv(R)
 assert yq
 if not Ssite:
  yq=y_gcd(y_gcd(yq,cv(A)),cv(C))
 if len(yq)<2:return []
 if len(yq)==2:y=-div(yq[0],yq[1])
 else:
  assert len(yq)==3
  y=Ring2(div(yq[0],yq[2]),div(yq[1],yq[2])).gen()
 out=[]
 for rear,sgn in case:
  try:out+=chart(F0,front,Ssite,y,rear,sgn)
  except YSplit as ob:
   for y1 in ob.ys:out+=chart(F0,front,Ssite,y1,rear,sgn)
 return out
def check_fifth_twins():
 for front in (True,False):
  a,b,ha,hb,hs,d,W,A,B,C,D,M=LF.front_data(front)
  for x,H in ((a,ha),(b,hb),(LF.s,hs)):
   f=B.compose(LF.Y,x);g=D.compose(LF.Y,x)
   assert not (A.compose(LF.Y,x)+f*H)
   assert not (C.compose(LF.Y,x)+g*H)
   assert FF.strip(FF.Gcd(FF.w(f),FF.w(g)),FF.w(d)).degree()==0
 print("Literal row five has no repeated-clock fiber",flush=True)

def run():
 check_fifth_twins()
 for front,Ssite in product((True,False),repeat=2):
  M0=scalar_proj(front,Ssite)
  for M in M0:
   through=through_ys(F(M),front,Ssite,((True,1),(False,1),(False,-1)))
   assert not through
   print("excluded singleton pitch",front,Ssite,M.degree(),flush=True)
if __name__=='__main__':run()

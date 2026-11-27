"""Projection for the one repeated discrepancy clock of a ten-stage endpoint pair."""
from pathlib import Path
import sys
research=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(research/name) for name in
             ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
              "sdirk-eight-half-arithmetic-quadratic")]
import literal_front as LF
from star_projection import *
from itertools import product

def evaluate(f,x,y):
 return sum(Rat.k(v)*x**i*y**j for (i,j,k),v in f.items() if not k)
def node_factor(nodes):
 p=[1]
 for x in nodes:p=mul(p,[-x,1])
 return p
def add(a,b):
 n=max(len(a),len(b));return trim([x+y for x,y in zip(a+[0]*(n-len(a)),b+[0]*(n-len(b)))])
def sc(a,k):return trim([k*x for x in a])
def I(p):
 return sum(v*Q(1,j+1) for j,v in enumerate(p))
def beam(i,j,k):
 if i>j and j<=k<i:return Q(1,i+j-k)
 if j>i and i<=k<j:return -Q(1,i+j-k)
 return Q(0)
def Bop(d,p):
 return [sum(a*b*beam(i,j,k) for i,a in enumerate(d) for j,b in enumerate(p)) for k in range(5)]
def nodal6(xs):
 P6=node_factor(xs);h0=I(P6);h1=I([0]+P6)
 D=add(sc([0]+P6,h0),sc(P6,-h1))
 assert I(D)==0
 return D,h0,h1
def cross(B,d):
 # equality of lines, including when the degree of B drops.
 return [B[i]*d[-1]-B[len(d)-1]*d[i] for i in range(len(d)-1)]+B[len(d):]
def rear_ratio(q,p,c,d,k,l):
 return l*ev(q,d)*ev(p,c)-k*ev(q,c)*ev(p,d)

def model(front,rear,sign,yphase):
 a,b,ha,hb,hs,d,W,A,B,C,D,M=LF.front_data(front)
 c,e,k,l,_=LF.end(sign,rear);c,e=1-c,1-e
 a0,b0=a,b
 a,b,ha,hb,c,e,k,l=map(Rat.k,(a,b,ha,hb,c,e,k,l))
 yctx=None
 if front:
  y=s*Q(3,2)-Q(1,4) if yphase==0 else Q(103,72)-s
  ylead=one
 else:
  W0=W.exquo(d.exquo((LF.s-a0)*(LF.s-b0)))
  yy=[sum(Rat.k(v)*s**i for (i,j,z),v in W0.items() if j==ell and not z) for ell in range(3)]
  ylead=yy[2]
  yctx=Ring2(yy[0]/yy[2],yy[1]/yy[2])
  y=yctx.gen()
 H4=evaluate(hs,s,y)
 B4=evaluate(B,s,y)
 H5=-evaluate(A,s,y)/B4
 rows=[Rv(z) for z in (a,b,s)]
 dets=det(rows)
 pegs=(a,b,s,y,c,e)
 dnod,h0,h1=nodal6(pegs)
 raw=[ylead,B4,dets,evaluate(d,s,y),s-a,s-b,y-a,y-b,y-s,s-c,y-c,s-e,y-e,h0]
 return (a,b,s,y,c,e),(ha,hb,H4,H5),k,l,rows,dets,dnod,raw,yctx

from check_star_family import Rv,Lpoly

def project(front,rear,sign,yphase,r_index,degree,cache=None):
 (a,b,s,y,c,e),h,k,l,rows,dl,D,raw,Y=cache or model(front,rear,sign,yphase)
 xx=[a,b,s,y];rx=xx[r_index]
 qL=[-rx,one]
 qA=[zero,-rx,one];qB=[rx,-one,zero]
 def gen(q):
  A0=cramer(rows,[v*ev(q,x) for v,x in zip(h[:3],xx[:3])])
  return [sum(A0[j]*(Lpoly[j][i] if i<len(Lpoly[j]) else 0) for j in range(3))/dl for i in range(6)]
 pL=gen(qL)
 G0=ev(pL,y)-h[3]*ev(qL,y)
 base=list(raw)
 if degree==1:
  q,p=qL,pL
  constr=[G0]
  R0=q
 else:
  A,B=gen(qA),sc(pL,-1)
  F0=ev(A,y)-h[3]*ev(qA,y)
  F1=-G0
  if not F1:
   # In this rare split chart the first equation must hold identically in xi.
   assert F0
   constr=[F0]
   q,p,R0=qL,pL,qL
  else:
   base.append(F1)
   p=add(sc(A,F1),sc(B,-F0))
   q=add(sc(qA,F1),sc(qB,-F0))
   R0=mul(qL,mul([F0,F1],[F0,F1]))
   constr=[]
 if degree==1 or F1:
  constr.append(rear_ratio(q,p,c,e,k,l))
  bcz=Bop(D,p)
  assert not bcz[-1]
  constr+=cross(bcz,R0)
 # All nonzero polynomial outputs vanish on every regular candidate. A norm
 # enlarges the s projection but never drops a good root.
 polys=[normP(z) for z in constr if z]
 H=gcds(polys)
 baseP=sf(__import__('functools').reduce(lambda a,b:a*b,[normP(g)*denomP(g) for g in base if g]))
 for z in constr:
  assert stripq(denomP(evalnorm(z)),baseP).degree()==0
 candidate=sf(baseP*H)
 rem=stripq(sf(H),baseP)
 return candidate,rem,(front,rear,sign,yphase,r_index,degree),len(polys)

def charts():
 for front,rear,sign in product((True,False),(True,False),(1,-1)):
  if rear and sign==-1:continue
  for yy in ((0,1) if front else (-1,)):
   z=model(front,rear,sign,yy)
   for ri,deg in product(range(4),(1,2)):
    A,B,key,k=project(front,rear,sign,yy,ri,deg,z)
    assert B.degree()==0 and A.degree()<=88
    assert k==(5 if deg==1 else 4)
    yield key,A

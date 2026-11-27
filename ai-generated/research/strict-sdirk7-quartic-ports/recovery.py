#!/usr/bin/env python3
"""Exact reflection quartic pole atlas with one deliberately forced rational early clock."""
from flint import fmpq_poly,fmpq,nmod_poly
from math import isqrt
from fractions import Fraction as Q
from collections import Counter
from itertools import product

def data(mode):
 if mode=='Q':
  cast=lambda v:fmpq(v.numerator,v.denominator)
  poly=lambda *v:fmpq_poly([cast(a) if isinstance(a,Q) else a for a in v])
  iv=lambda a:1/a
  get=lambda x:Q(int(x.numerator),int(x.denominator))
 else:
  cast=lambda v:v.numerator*pow(v.denominator,-1,19)%19 if isinstance(v,Q) else int(v)%19
  poly=lambda *v:nmod_poly([cast(a) for a in v],19)
  iv=lambda a:pow(int(a)%19,-1,19)
  get=lambda a:int(a)%19
 return cast,poly,iv,get

def frame(m,c,mode='Q'):
 f,P,iv,get=data(mode)
 m,c=f(m),f(c)
 if not m:return
 X=P(0,1); x=X-m
 p3=x**3-f(Q(3,5))*m*m*x
 p4=x**4-f(Q(6,7))*m*m*x*x+f(Q(3,35))*m**4
 fourth=lambda a,b,d,e,k:P(11*a+6*b+6*d+12*e+36*k,
    -8*a-7*b-12*d-30*e-96*k,a+b+2*d+6*e+24*k)
 F3=fourth(*[p3[i] for i in range(5)]);F4=fourth(*[p4[i] for i in range(5)])
 if not F3(c):return
 delta=-F4(c)*iv(F3(c))
 g=p4+delta*p3
 if not (g(c) and g(1)):return
 jr=(g-g(1))//(X-1)
 B=(p3*(jr+X+g[3]+5))%g
 A=(X*B)%g
 P0=(A(c)*g-g(c)*A)//(X-c)
 P1=(B(c)*g-g(c)*B)//(X-c)
 assert (A(c)*g-g(c)*A)%(X-c)==0 and (B(c)*g-g(c)*B)%(X-c)==0
 d0,d1,d2,d3=[g[i] for i in range(4)]
 G=g(1)
 t0=P(d0+2*d3+10+2*G,d1-6*d3-28-4*G,d2+5*d3+19+G)
 t1=P(-d3-5-G,d3+4,1)
 return (g,delta,A,B,P0,P1,t0,t1)

def sqrtq(a):
 if a<0:return None
 b,c=isqrt(a.numerator),isqrt(a.denominator)
 if (b*b,c*c)==(a.numerator,a.denominator):return Q(b,c)

def recover(m,c,a,s,st):
 f,P,iv,get=data('Q')
 g,delta,A,B,P0,P1,t0,t1=s
 a,c_,m_=f(a),f(c),f(m)
 if a in (c_,1) or not (P1(a) and g(a)):return
 h=P0(a)/P1(a)
 if h in (a,c_,1) or not (t1(h) and A(c_)-h*B(c_)):return
 M=-t0(h)/t1(h)
 S3=(P0-h*P1)/(A(c_)-h*B(c_))
 assert S3.degree()==3 and S3[3]==1 and S3(a)==0
 X=P(0,1)
 Q2=S3//(X-a)
 D=Q2[1]**2-4*Q2[0]
 ds=sqrtq(get(D)); k=sqrtq(get(M+2))
 st['rational-port']+=1
 if ds:st['split-clock']+=1
 if k:st['split-suffix']+=1
 if not (ds and k):return
 u=2+k;v=2-k
 b2,b3=(-get(Q2[1])+ds)/2,(-get(Q2[1])-ds)/2
 ys=[get(a),b2,b3,c,v,u,Q(1)]
 if len(set(ys))!=7 or any(y==get(h) for y in ys):return
 return (2*m,u,c,ys,get(h),get(delta))

def mirror_ports(m,c,s):
 f,P,iv,get=data('Q')
 _,_,_,_,P0,P1,_,_=s
 X=P(0,1)
 m=f(m)
 tr=lambda p,sgn:sum((p[i]*(m+sgn*X)**i for i in range(len(p))),start=P(0))
 F=tr(P0,1)*tr(P1,-1)-tr(P1,1)*tr(P0,-1)
 if not F:return
 assert F.degree()<=5 and not any(F[i] for i in (0,2,4))
 t=P(F[1],F[3],F[5])
 for p0,k in t.roots():
    q=sqrtq(get(p0))
    if q:
       yield get(m)+q
if __name__=='__main__':
 st=Counter()
 fam=[Q(x,y) for x,y in [(1,1),(2,1),(3,1),(-1,1),(1,2),(3,2),(-1,2),(2,3),(3,4),(4,3),(5,4),(4,5),(8,3),(12,13)]]
 for m in fam:
  for c in set([Q(i,j) for i,j in [(0,1),(-1,1),(2,1),(3,1),(4,1),(-2,1),(-3,1),(1,2),(3,2),(5,2),(3,4),(-3,2)]]
       +[m,2*m,2*m-1,1+m,m-1,2-m,m/2,3*m/2,2*m+1,Q(1942,1399),Q(13829,30143)]):
   s=frame(m,c)
   if not s:continue
   for a in set([m,Q(0),2*m,2*m-1,2*m-c,m+c,(m+c)/2,-c,1+c,2+c,m-c,m/2,3*m/2,*mirror_ports(m,c,s)]):
    x=recover(m,c,a,s,st)
    if x:
      print('EXACT CORE',x,flush=True); raise SystemExit
 print(st,flush=True)

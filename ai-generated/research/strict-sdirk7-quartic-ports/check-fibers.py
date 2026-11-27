#!/usr/bin/env python3
from recovery import data,frame,Q
from math import lcm,gcd,prod
from sympy import primerange
from flint import fmpq_poly
f,P,iv,get=data('Q');X=P(0,1)
def pair(s):
 g,delta,A,B,P0,P1,t0,t1=s
 Bez=[P(0),P(0),P(0)]
 for i in range(1,4):
   for j in range(i):
      a=P0[i]*P1[j]-P1[i]*P0[j]
      for k in range(i-j):
        Bez[i-1-k]+=a*X**(j+k)
 qs=Bez[1]**2-4*Bez[0]*Bez[2]
 # h=P0/P1. Write S = 2 - t0(h)/t1(h).
 D=sum((t1[i]*P0**i*P1**(2-i) for i in range(3)),start=P(0))
 N=2*D-sum((t0[i]*P0**i*P1**(2-i) for i in range(3)),start=P(0))
 gd=N.gcd(D);assert gd
 N,D=N//gd,D//gd
 return N*D,qs,N,D,Bez

def squareclass(p):
  a,fs=p.factor()
  q=a*prod((f for f,k in fs if k%2),start=P(1))
  D=lcm(*(int(q[i].denominator) for i in range(len(q))))
  q=q*(D*D)
  return [int(x) for x in q.coeffs()]
def hor(a,x,q):
 r=0
 for v in a[::-1]:r=(r*x+v)%q
 return r
def rev(f):
    return list(reversed(f+([0] if len(f)%2==0 else [])))
def normal(F,p):
    g=gcd(*F);k=0
    while g%p==0:g//=p;k+=1
    return [v//p**(k-k%2) for v in F]
def sieve(xs,p,n):
    A,B=(normal(x,p) for x in xs)
    sts=[[i for i in range(p)],[0]]
    Q=p
    for k in range(n):
      sq={i*i%Q for i in range(Q)}
      C0,D0=A,B;C1,D1=rev(A),rev(B)
      rr=[]
      for ss,C,D in zip(sts,[C0,C1],[D0,D1]):
        rr.append([x for x in ss if hor(C,x,Q) in sq and hor(D,x,Q) in sq])
      if not any(rr):return k+1
      if k>1 and any(hor(C,x,Q) and hor(D,x,Q) and hor(C,x,Q)%p and hor(D,x,Q)%p for ss,C,D in zip(rr,[C0,C1],[D0,D1]) for x in ss):return
      sts=[[x+i*Q for x in aa for i in range(p)] for aa in rr]
      Q*=p

cases=[(3,4,2,8),(1,3,19,1),(3,Q(3,4),2,6),(3,Q(-3,2),2,6),(Q(1,2),Q(1,2),3,4),
       (Q(3,2),Q(5,2),23,1),(Q(3,2),Q(3,4),13,1),(Q(-1,2),Q(3,2),47,1),
       (1,Q(1942,1399),19,1),(2,0,2,8),(1,2,3,2)]
if __name__=='__main__':
  for m,c,ell,k in cases:
    z=frame(Q(m),Q(c)); assert z
    g,d,A,B,P0,P1,t0,t1=z
    assert P0.gcd(P1).degree()==0 and t0.gcd(t1).degree()==0
    U,Q2,N,D,Bez=pair(z)
    assert N.degree()==D.degree()==6 and Q2.degree()==4
    xs=[squareclass(U),squareclass(Q2)]
    assert sieve(xs,ell,k)==k
    if (m,c) in ((3,4),(1,Q(1942,1399))):
       aa=[normal(F,ell) for F in xs]
       q=ell**k
       reduced=[[x%q for x in ff] for ff in aa]
       import re
       from pathlib import Path
       sr=Path(__file__).resolve().parents[2]/"lean/RKCert/Research/SDIRKSevenQuarticPort.lean"
       s=sr.read_text()
       tag="Wide" if m==3 else "Old"
       for j,li in zip(("U","Q"),reduced):
          match=rf"def receipt{tag}{j} : List ℤ := \[([^\]]+)\]"
          assert [int(v) for v in re.search(match,s).group(1).split(",")]==li
       sq={x*x%q for x in range(q)}
       for a,b in [aa,[x[::-1] for x in aa]]:
          assert all(not (hor(a,x,q) in sq and hor(b,x,q) in sq) for x in range(q))
    print(m,c,"no rational port: no simultaneous square classes mod",ell**k)

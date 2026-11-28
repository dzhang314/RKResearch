#!/usr/bin/env python3
"""Guarded exact pressure map and a unit-Jacobian 17-power lift."""
from residue import M,scalar,dot
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations
from math import prod
import json
import sys
D=Path(__file__).resolve().parent
BASE=D.parent/'erk10-sixteen-f17'
sys.path.insert(0,str(BASE))
from verify import replay
P=17
C0=(1,7,15,10,11,16,2,8,14)
X0=(10,*C0[1:])
CH=((5,4),(6,4),(6,5),(7,4),(7,5))
def solve(A,T,guard=None):
 n=len(T)
 A=[list(r)+[u]for r,u in zip(A,T)]
 piv=[]
 assert len(A)==n and all(len(r)==n+1 for r in A)
 for i in range(n):
  j=next((j for j in range(i,n)if int(A[j][i])%17),None)
  if j is None:return
  A[i],A[j]=A[j],A[i];a=A[i][i]
  piv.append((j,int(a)%17))
  A[i]=[x/a for x in A[i]]
  for j in range(n):
   if i==j:continue
   a=A[j][i]
   A[j]=[x-a*y for x,y in zip(A[j],A[i])]
 assert all(A[i][j]==(i==j)for i in range(n)for j in range(n))
 if guard is not None:guard.extend(piv)
 return [row[-1]for row in A]
def decode(path):
 return {k:[[list(map(F,q))for q in r]for r in d]for k,d in json.loads(Path(path).read_text()).items()}
PRE=decode(D/'prefix-algebraic.json')
def chart(raw,m,pick=None,emit=False,guard=None):
 M.p=m
 theta=M(raw[0]);c=[M(1),*map(M,raw[1:])]
 assert len(c)==9 and int(theta)%17 and len({int(x)%17 for x in [M(0),*c]})==10
 sites=[M(0),*c]
 W,w0,_=scalar(sites)
 assert all(int(x)%17 for x in W.values())
 if guard is not None:
  guard["fixed numerical denominators"]={str(x):x%17 for x in range(1,11)}
  guard["theta, alias"]=[int(theta)%17,int(c[-1])%17]
  guard["cardinal difference products"]=[int(prod(x-y for y in sites if y!=x))%17 for x in sites]
  guard["cardinal masses"]=[int(W[x])%17 for x in sites]
 def solv(tag,A,b):
  note=[]
  x=solve(A,b,note)
  if x is not None and guard is not None:
   prev=guard.setdefault(tag,note)
   assert prev==note
  return x
 cof={x:w0[x]*(x-1) for x in c[1:]}
 w=[W[x]for x in c]
 y=[1-x for x in c]
 Z=M(0);O=M(1)
 ub=-w[1]*y[1]**2/(2*cof[c[1]])
 U=[Z]+[ub*cof[x]for x in c[1:]]
 xu=[a*x for a,x in zip(U,c)]
 M0=[[a*x**k for a,x in zip(w,y)]for k in range(5)]
 K=[[Z]*9 for _ in range(9)]
 K[1][0]=M0[1][1]/w[0]
 K[2][:2]=solv("first two donors",[a[:2]for a in M0[:2]],[M0[1][2],M0[2][2]/2+U[2]])
 def dfn(j):
  return [(dot(K[i],M0[2])-M0[3][i]/3 if j==0 else dot(K[i],U))for i in (1,2)]
 T0=[[U[i],xu[i]]for i in (1,2)]
 G,H=[[dot(v,(a,b))for a,b in zip(U,xu)]for v in (solv("two density reads",T0,dfn(0)),solv("two density reads",T0,dfn(1)))]
 RR=[*M0[:3],U]
 def target(i):return [M0[1][i],M0[2][i]/2+U[i],M0[3][i]/3+G[i],H[i]]
 K[3][:3]=solv("first three donors",[r[:3]for r in RR[:3]],target(3)[:3])
 eq1=dot(K[3],U)-H[3]
 S=[r[:4]for r in RR]
 for i in range(4,9):K[i][:4]=solv("first four donors",S,target(i))
 free=[]
 for i,j in CH:
  vk=solv("first four donors",S,[-r[j]for r in RR])+[Z]*5
  vk[j]=O
  free.append(vk)
 coeff=lambda a,b:M(a)+M(b)*theta
 def apply_pfx(q,x):return sum(coeff(*a)*x**j for j,a in enumerate(q))
 psi=[[apply_pfx(q,theta*x/c[-1])for x in c]for q in PRE['H6']]
 KRaw=[[dot(r,vals)-(M0[4][i]/4 if j==0 else Z)for i,r in enumerate(K)]
       for j,vals in enumerate((M0[3],xu))]
 ts=[]
 C=[]
 for vals,res in zip((M0[3],xu),KRaw):
  for s in psi:
   ts.append(-dot(s,res))
   C.append([s[i]*dot(v,vals)for (i,_),v in zip(CH,free)])
 if pick is None:
  for rrs in combinations(range(6),5):
   tt=solve([C[i]for i in rrs],[ts[i]for i in rrs])
   if tt is not None:
    pick=rrs
    break
  assert pick is not None
 else:
  tt=solv("five terminal equations", [C[i]for i in pick],[ts[i]for i in pick])
  assert tt is not None
 omit=next(i for i in range(6)if i not in pick)
 eq2=dot(C[omit],tt)-ts[omit]
 eq0=3*theta*theta-15*theta+20
 E=tuple(map(int,(eq0,eq1,eq2)))
 if not emit:return E,pick
 assert E==(0,0,0)
 for (i,j),a,r in zip(CH,tt,free):
  K[i]=[x+a*y for x,y in zip(K[i],r)]
 assert all([dot(K[i],r)for r in RR]==target(i) for i in range(9))
 assert all(dot(q,[dot(r,M0[3])-M0[4][i]/4 for i,r in enumerate(K)])==0 for q in psi)
 assert all(dot(q,[dot(r,xu)for r in K])==0 for q in psi)
 sc=c[-1]/theta
 A0=[[coeff(*a)*sc for a in r]for r in PRE['A']]
 Pi=[[coeff(*a)/sc**k for a in r]for k,r in enumerate(PRE['Pi'])]
 seq=c[::-1];cols=range(9)
 BB=[[K[8-j][8-i]if j<i else Z for j in cols]for i in cols]
 cross=[]
 for i,x in enumerate(seq):
  h=[x**(k+1)/(k+1)-dot(BB[i],[z**k for z in seq]) for k in range(5)]
  cross.append([dot(h,[q[j]for q in Pi])for j in range(8)])
 assert cross[0]==A0[-1]+[Z] and not any(BB[0])
 A=[list(r)+[Z]*(16-len(r))for r in A0]
 for a,b in zip(cross[1:],BB[1:]):
  a[7]+=b[0];A.append(a+b[1:])
 b=[W[Z]]+[Z]*6+[w[-1]]+w[-2::-1]
 assert len(A)==len(b)==16 and all(not any(r[i:])for i,r in enumerate(A))
 _,count,defect=replay([[int(x)for x in r[:i]]for i,r in enumerate(A)],[int(x)for x in b],m)
 assert count==1205 and defect%17==2
 return A,b,defect,pick
def derivative(pick):
 m=17**2
 C,_=chart(X0,m,pick)
 J=[]
 for j,u in enumerate(X0):
  Y=list(X0);Y[j]+=17
  D,_=chart(Y,m,pick)
  a=[d-c for c,d in zip(C,D)]
  assert all(x%17==0 for x in a)
  J.append([x//17%17 for x in a])
 return J
def main(k=5,emit=None):
 E,pick=chart(X0,17)
 assert E==(0,0,0)
 guard={}
 Z=chart(X0,17,pick,True,guard)
 assert all(guard[key] for key in guard)
 print('All residue guards (row swaps zero-based, then pivot mod17):',json.dumps(guard,sort_keys=True))
 baseline=json.loads((BASE/'tableau.json').read_text())
 assert [[[str(x)for x in r[:i]]for i,r in enumerate(Z[0])],list(map(str,Z[1]))]==[baseline['A'],baseline['b']]
 print('Original literal frozen witness regenerated; pivot terminal equations',pick)
 J=derivative(pick)
 print('Mod-17 pressure derivatives by variable',J,flush=True)
 M.p=17
 for i,j in combinations(range(1,len(X0)),2):
  x=[tuple(map(M,a))for a in zip(J[0],J[i],J[j])]
  if solve(x,[M(0)]*3)is not None:
   print('chosen variables',0,i,j,'Jacobian',x,flush=True)
   inds=(0,i,j);jac=[[int(v)for v in r]for r in x]
   assert inds==(0,3,5) and jac==[[11,0,0],[0,11,5],[1,2,13]]
   determinant=jac[0][0]*(jac[1][1]*jac[2][2]-jac[1][2]*jac[2][1])
   assert determinant%17==1
   break
 else:raise ValueError('no invertible Jacobian')
 X=list(X0);a=17
 for v in range(2,k+1):
  f,_=chart(X,a*17,pick)
  assert all(x%a==0 for x in f)
  M.p=17
  dy=solve([list(map(M,r))for r in jac],[-M(b//a)for b in f])
  for j,y in zip(inds,dy):X[j]+=a*int(y)
  a*=17
  b,c,z,_=chart(X,a,pick,True)
  val={'prime':17,'exponent':v,'modulus':a,'parameters':X,
       'A':[[int(x)for x in r[:i]]for i,r in enumerate(b)],'b':[int(x)for x in c],
       'bush_failure':z}
  literal=D/'literals'/('mod17pow'+str(v)+'.json')
  if literal.exists():assert val==json.loads(literal.read_text())
  if emit:
   emit.mkdir(parents=True,exist_ok=True)
   (emit/literal.name).write_text(json.dumps(val,indent=2)+'\n')
  print('exact literal replay mod 17^'+str(v),'root/mesh parameters',X,'unit bush defect',z,flush=True)
if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--exponent',type=int,default=5)
 p.add_argument('--emit',type=Path)
 a=p.parse_args()
 main(a.exponent,a.emit)

#!/usr/bin/env python3
from flint import nmod_mpoly_ctx,fmpq,fmpz_poly
from math import gcd,lcm,factorial
from multiprocessing import get_context
from collections import Counter
from time import monotonic
from pathlib import Path
from math import isqrt
import argparse
import os
import json

parser=argparse.ArgumentParser()
parser.add_argument("--work-dir",type=Path,default=Path(".projection-work"))
parser.add_argument("--workers",type=int,default=3)
parser.add_argument("--save-full",action="store_true")
args=parser.parse_args()
assert args.workers>=1
D=args.work_dir
TITLE=Path(__file__).with_name("primitive-z-degree-324.json")
def nextprime(p):
 q=p+1 if p%2==0 else p+2
 while not all(q%d for d in range(3,isqrt(q)+1,2)):
  q+=2
 return q

start=monotonic()

def ints(f):
 r=[fmpq(t[3]) for t in f]
 den=lcm(*(int(q.denominator) for q in r))
 num=[int(q.numerator)*(den//int(q.denominator)) for q in r]
 gs=gcd(*num)
 return {tuple(t[:3]):v//gs for t,v in zip(f,num)}

data=json.loads((D/'two-polynomials.json').read_text())
A,B=ints(data['R']),ints(data['S'])
m=max(t[1] for t in A)
n=max(t[1] for t in B)
Hmax=max(t[0] for t in A)*n+max(t[0] for t in B)*m
la=sum(map(abs,A.values())).bit_length()
lb=sum(map(abs,B.values())).bit_length()
bound=la*n+lb*m+factorial(m+n).bit_length()+2

def project(p):
 K=nmod_mpoly_ctx.get(['z','c','s'],p,'lex')
 a=K.from_dict({t:v%p for t,v in A.items() if v%p})
 b=K.from_dict({t:v%p for t,v in B.items() if v%p})
 if int(a.degrees()[1])!=m or int(b.degrees()[1])!=n:
  return (p,[])
 c=a.resultant(b,'c')
 q=c.to_dict()
 if c.is_zero(): return (p,[0])
 return (p,[int(q.get((i,0,0),0)) for i in range(1+int(c.degrees()[0]))])

def main():
 # Do not trust a resumed CRT accumulator: every included residue is generated here.
 rest=[];M=1;lst=[];last=536870900
 print('Sylvester sizes',m,n,'degree cap',Hmax,'rigorous coefficient bit cap',bound,'resuming',len(lst),flush=True)
 with get_context('fork').Pool(args.workers) as pool:
  batches=0
  while M.bit_length()<=bound:
   primes=[]
   for i in range(12):
    last=int(nextprime(last))
    primes.append(last)
   for p,res in pool.map(project,primes):
    if not res:continue
    ll=max(len(res),len(rest));rest.extend([0]*(ll-len(rest)));res.extend([0]*(ll-len(res)))
    E=pow(M,-1,p)
    rest=[a+M*((b-a%p)*E%p) for a,b in zip(rest,res)]
    M*=p;lst.append(p)
   batches+=1
   if batches%2==0:
    print('CRT',len(lst),M.bit_length(),'/',bound,'seconds',round(monotonic()-start,1),'degree',len(rest)-1,flush=True)
 O=fmpz_poly([a if a<M//2 else a-M for a in rest])
 print('reconstruction complete degree',O.degree(),'height',max(map(abs,O)).bit_length(),flush=True)
 assert (m,n,Hmax,bound)==(9,81,3987,11540)
 assert O.degree()==3691
 assert M.bit_length()>bound
 H=fmpz_poly([int(x) for x in json.loads(TITLE.read_text())])
 assert H.degree()==324 and H(8)%19==0 and H.gcd(H.derivative()).degree()==0
 assert O%H==0
 assert O(8)%19==0 and O.derivative()(8)%19!=0
 assert (O//H)(8)%19!=0
 if args.save_full:
  (D/'integer-projection.json').write_text(json.dumps([str(x) for x in O]))
 print("exact integer projection: the literal degree-324 polynomial divides, and z=8 is simple modulo 19")

if __name__=='__main__':
 import sys
 sys.set_int_max_str_digits(0)
 main()

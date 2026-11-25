#!/usr/bin/env python3
"""Integer-index saturation for the genuine degree-five numerator.
If its clock-zero entry is nonzero, a viable cubic must have a common divisor
of degree at least two with the pencil after the known knots 1,z are removed.
At such a point every first derivative of the fixed Sylvester determinant
vanishes, independently of multiplicities and field algebraic closure.
"""
from pathlib import Path
from math import gcd
import json,sys
from functools import reduce
import exact_index as EI
from check_pencil_projection import F,J,ev,res,interp,trim,cubic_pair
def q(t,z,shift,direction):
 f=ev(F,t);j=ev(J,t);h=[J[i]*f-F[i]*j for i in range(7)];w=[0]*7
 for i in range(4,-1,-1):w[i]=t**i*h[i+2]+(1+z)*w[i+1]-z*w[i+2]
 P=[12*z-15*z*z,60*z*z-24*z-18,-10*(5*z*z+4*z-6),15*(4*z-3)]
 if direction<4:P[direction]+=shift
 else:w[direction-4]+=shift
 return res(w[:5],P,4,3)
def result(src,out,deriv):
 # W_i has degree <=10 in t and <=4 in z; 3 W plus 4 P gives
 # Q bidegree <=(30,20), and T z-degree <=30*6+5*20=280.
 def Q(t,z):
    if deriv<0:return q(t,z,0,0)
    f=interp([q(t,z,i,deriv) for i in range(5)]);return (f+[0,0])[1]
 qtab=EI.bi(30,20,Q)
 def live(z):return cubic_pair(z)[0],[ev(co,z) for co in qtab]
 T=interp([EI.fixed(*live(z),5,30) for z in range(281)])
 for z in (-3,7,281):assert ev(T,z)==res(*live(z),5,30)
 R=next(s for s in json.loads((src/'projection_data.json').read_text()) if s['name']=='cubic')['R']
 N=EI.fixed(R,T,len(R)-1,len(T)-1)
 print('dir',deriv,'degree',len(T)-1,'Nbits',abs(N).bit_length(),flush=True)
 (out/('clean_index_'+str(deriv)+'.json')).write_text(json.dumps({'dir':deriv,'T':T,'index_hex':hex(N)},separators=(',',':'))+'\n')
 return N
if __name__=='__main__':
 src,out=Path(sys.argv[1]),Path(sys.argv[2]);c=json.loads((out/'exact_cubic_outer.json').read_text());R=c['R'];raw=abs(int(json.loads((out/'index_cubic.json').read_text())['raw_hex'],16))
 p0=sum(r*4**i*5**(len(R)-1-i) for i,r in enumerate(R));v0=gcd(raw,p0)
 def strip(n):
    for p in (2,3,5,7,11,13):
       while not n%p:n//=p
    return n
 print('constant-zero branch gcd after small primes:',strip(v0),flush=True)
 a=raw
 for d in [int(j) for j in sys.argv[3:]]:
    a=gcd(a,result(src,out,d));v=strip(a);print('surviving GCD bits',v.bit_length(),('N='+str(v) if v.bit_length()<2000 else ''),flush=True)

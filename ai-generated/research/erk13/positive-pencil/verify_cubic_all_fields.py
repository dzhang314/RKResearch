#!/usr/bin/env python3
"""Prove the two extra projected integers exactly without SymPy.
Compute the generic complementary quartic using complete homogeneous symmetric
polynomials rather than the emitter's division recurrence. For the directional
derivative, sum the four ordinary diagonal cofactors of the Sylvester matrix,
rather than interpolating the lambda-polynomial. Verify all integer outer
interpolation values and then independently certify each huge signed index
by prime-field remainders, CRT and the squared Hadamard bound.
"""
from pathlib import Path
import json,sys
from math import isqrt,gcd
sys.path.insert(0,sys.argv[1])
from verify_indices import fieldres
from check_pencil_projection import F,J,ev,trim,interp,det,res,cubic_pair
def inner(t,z,der):
 f=ev(F,t);j=ev(J,t)
 w=[sum(t**(k-2)*(J[k]*f-F[k]*j)*sum(z**q for q in range(k-i-1)) for k in range(i+2,7)) for i in range(5)]
 p=[12*z-15*z*z,60*z*z-24*z-18,-10*(5*z*z+4*z-6),15*(4*z-3)]
 a=[[0]*i+p+[0]*(3-i) for i in range(4)]+[[0]*i+w+[0]*(2-i) for i in range(3)]
 if not der:return det(a)
 return sum(det([[x for j,x in enumerate(row) if j!=k] for i,row in enumerate(a) if i!=k]) for k in range(4))
def smooth(n):
 n=abs(n);out=[]
 for p in [2,3,5,7,11,13]:
    e=0
    while n%p==0:n//=p;e+=1
    out.append(e)
 assert n==1
 return out
def verify(src,dst):
 raw=int(json.loads((dst/'index_cubic.json').read_text())['raw_hex'],16);D=[raw]
 R=json.loads((dst/'exact_cubic_outer.json').read_text())['R']
 p0=sum(v*4**i*5**(len(R)-1-i) for i,v in enumerate(R))
 print('P(0)=0 branch: smooth gcd(D_old,5^50 R(4/5)) exponents =',smooth(gcd(raw,p0)),flush=True)
 limit=10**6;sieve=bytearray(b'\1')*(limit+1);sieve[:2]=b'\0\0'
 for i in range(2,isqrt(limit)+1):
    if sieve[i]:sieve[i*i::i]=b'\0'*((limit-i*i)//i+1)
 primes=[p for p in range(limit,1,-1) if sieve[p]]
 for dire in (-1,0):
    d=json.loads((dst/('clean_index_'+str(dire)+'.json')).read_text());T=d['T'];N=int(d['index_hex'],16);der=dire==0
    rows=[interp([inner(t,z,der) for t in range(31)]) for z in range(21)]
    coeff=[interp([row[i] if i<len(row) else 0 for row in rows]) for i in range(31)]
    for z in range(281):assert res(cubic_pair(z)[0],[ev(row,z) for row in coeff],5,30)==ev(T,z)
    print('cofactor' if der else 'complement','full 31x21 inner and 281 outer integer interpolation grid passed; T degree',len(T)-1,flush=True)
    B=sum(c*c for c in R)**(len(T)-1)*sum(c*c for c in T)**(len(R)-1);assert N and N*N<=B;mod=1
    for k,p in enumerate(primes,1):
       assert fieldres(R,T,p)==N%p
       mod*=p
       if mod*mod>4*B:break
    else:raise AssertionError('missing primes')
    D.append(N);print('index bits',abs(N).bit_length(),'signed CRT residues',k,'modulus bits',mod.bit_length(),flush=True)
 print('P(0) nonzero branch: smooth gcd(D_old,D_complement,D_cofactor) exponents =',smooth(gcd(gcd(D[0],D[1]),D[2])),flush=True)
if __name__=='__main__':verify(Path(sys.argv[1]),Path(sys.argv[2]))

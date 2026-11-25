#!/usr/bin/env python3
"""Independent integer indices by interpolation and proved CRT/Hadamard bounds.
No SymPy, and no reliance on the subresultant routine used for discovery.
All physical projection polynomials are rechecked on a full interpolation grid
at their exact degree bounds using ordinary fraction-free Sylvester determinants.
"""
from pathlib import Path
import sys,json
from math import isqrt
sys.path.insert(0,sys.argv[1])
from check_pencil_projection import trim,res,ev,interp,F,J,quartic_forms
def inner(t,z):
 h=[t**i*(J[i]*ev(F,t)-F[i]*ev(J,t)) for i in range(7)]
 g=[12*z-15*z*z,60*z*z-24*z-18,-10*(5*z*z+4*z-6),15*(4*z-3)]
 return res(h,g,6,3)
def fieldres(f,g,p):
 # Ordered resultant with degrees fixed over the integers, including pad cases.
 m,n=len(f)-1,len(g)-1;A=trim([v%p for v in f]);B=trim([v%p for v in g]);da,db=len(A)-1,len(B)-1
 if da<m and db<n:return 0
 if da<0 or db<0:
    if m and n:return 0
    return pow(A[0],n,p) if not m and A else pow(B[0],m,p) if not n and B else 1 if not m+n else 0
 k=pow(A[-1],n-db,p) if da==m else pow((-1)**n*B[-1],m-da,p)
 while len(B)>1:
    a,b=len(A)-1,len(B)-1
    if a<b:
       if a*b%2:k=-k
       A,B=B,A;continue
    r=A[:];inv=pow(B[-1],-1,p)
    while len(r)>=len(B):
       u=r[-1]*inv%p;sh=len(r)-len(B)
       for j in range(len(B)-1):r[sh+j]=(r[sh+j]-u*B[j])%p
       r.pop()
       while r and not r[-1]:r.pop()
    if not r:return 0
    if a*b%2:k=-k
    k=k*pow(B[-1],a+1-len(r),p)%p
    A,B=B,r
 return k*pow(B[0],len(A)-1,p)%p
def run(src,dst):
 ds=json.loads((src/'integer_ports.json').read_text());pd={d['name']:d for d in json.loads((src/'projection_data.json').read_text())}
 limit=1000000;tab=bytearray(b'\1')*(limit+1);tab[:2]=b'\0\0'
 for i in range(2,isqrt(limit)+1):
    if tab[i]:tab[i*i::i]=b'\0'*((limit-i*i)//i+1)
 primes=[p for p in range(limit,1,-1) if tab[p]]
 for d in ds:
    n=d['name'];rmod=pd[n];zdata=json.loads((dst/('exact_'+n+'_outer.json')).read_text());R,T=zdata['R'],zdata['T']
    assert R==rmod['R'] and trim([v%1009 for v in T])==rmod['Tmod']
    origin=rmod['raw_origin_power'];content=rmod['raw_content'];m,v,bnd=(5,5,65) if n=='cubic' else (9,10,85)
    for z in range(bnd+1):
       a=[ev(c,z) for c in d['A']];c=[ev(b,z) for b in d['C']]
       assert res(a,c,m,v)==content*z**origin*ev(R,z)
    print(n,'primitive R independently verified on',bnd+1,'integer knots',flush=True)
    if n=='cubic':
       # Reconstruct each coefficient in z from independent 9x9 determinants.
       rows=[interp([inner(t,z) for t in range(34)]) for z in range(13)]
       B=[interp([row[i] if i<len(row) else 0 for row in rows]) for i in range(34)]
       m,v,bnd=5,33,258
    else:B=d['H'][0];m,v,bnd=9,14,137
    for z in range(bnd+1):
       assert res([ev(row,z) for row in d['A']],[ev(row,z) for row in B],m,v)==ev(T,z)
    print(n,'outer T verified on full',bnd+1,'integer knots',flush=True)
    N=int(json.loads((dst/('index_'+n+'.json')).read_text())['raw_hex'],16)
    sqBound=sum(c*c for c in R)**(len(T)-1)*sum(c*c for c in T)**(len(R)-1)
    assert N and N*N<=sqBound
    modulus=1
    for k,p in enumerate(primes,1):
       assert N%p==fieldres(R,T,p),(n,p)
       modulus*=p
       if modulus**2>4*sqBound:break
    else:raise AssertionError('insufficient pairwise coprime moduli')
    print(n,'index bits',abs(N).bit_length(),'certified by',k,'different prime residues, CRT modulus bits',modulus.bit_length(),'squared Hadamard bound bits',sqBound.bit_length(),flush=True)
    factors=sorted(p for p in primes if p>13 and not N%p)
    print(n,'all prime-index divisors in [17,1000000]',factors,flush=True)
if __name__=='__main__':run(Path(sys.argv[1]),Path(sys.argv[2]))

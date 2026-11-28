"""Independent proof-bound, checkpointed rational literal-fourth diagonal."""
from literal4_projection import projections
from geometric_outer import img,compiler
from rear67_exact import full_native
from flint import fmpz_poly
from sympy import nextprime
from math import gcd
from time import perf_counter
from pathlib import Path
import gzip,sys
sys.set_int_max_str_digits(0)

def image(A,B,p):
    V=img(A,B,p) if compiler() is not None else None
    return full_native(A,B,p) if V is None else V

def exact(A,B):
    ga,sa=A.degrees();gb,sb=B.degrees()
    C=ga*sb+gb*sa
    assert (ga,sa,gb,sb,C)==(96,33,136,43,8616)
    Bnd=sum(abs(int(x)) for x in A.to_dict().values())**sb*sum(abs(int(x)) for x in B.to_dict().values())**sa
    P=[];p=2**60;m=1
    while m<=2*Bnd:
        p=int(nextprime(p+1000));P.append(p);m*=p
    print('literal4 serial exact cap/bits/primes',C,Bnd.bit_length(),len(P),flush=True)
    M=1;Z=[0]*(C+1)
    assert image(A,B,P[0])==full_native(A,B,P[0])
    tt=perf_counter()
    for j,p in enumerate(P,1):
        V=image(A,B,p);assert V and len(V)==C+1
        b=pow(M,-1,p)
        for i,v in enumerate(V):Z[i]+=M*((v-Z[i])*b%p)
        M*=p
        if j%32==0 or j==len(P):
            print('literal4 exact CRT progress',j,M.bit_length(),round(perf_counter()-tt,2),flush=True)
    assert M==m and M>2*Bnd
    for i,z in enumerate(Z):
        if 2*z>=M:Z[i]=z-M
    assert all(abs(z)<=Bnd for z in Z)
    p=65537
    W=image(A,B,p)
    assert W==full_native(A,B,p) and all((x-y)%p==0 for x,y in zip(Z,W))
    h=next(i for i,z in enumerate(Z) if z)
    assert (C,h,Bnd.bit_length(),len(P))==(8616,1587,22819,381)
    c=gcd(*Z)
    assert Z[-1]
    print('literal4 exact degree valuation prime count',C,h,len(P),
          'primitive remaining',C-h,flush=True)
    U=Path('literal4-diagonal.gz')
    with gzip.open(U,'wt',encoding='utf-8') as f:
        f.writelines(str(z//c)+'\n' for z in Z[h:])
    return U

if __name__=='__main__':exact(*projections())

"""Reconstruct only the exact norm quotient and verify the whole product by bounds."""
from pathlib import Path
from ast import literal_eval
from math import prod
from time import perf_counter
from flint import nmod_poly
from sympy import nextprime
import gzip,sys
sys.set_int_max_str_digits(0)

def source():
    for l in Path('arith67-cover-plan.txt').read_text().splitlines():
        e,n,body=l.split(' ',2);i=body.index(']')
        names=literal_eval(body[:i+1]);F=list(map(int,body[i+1:].split()))
        yield F,int(e),int(n),names

def main():
    with gzip.open('arith67-oriented-exact.gz','rt',encoding='utf-8') as f:
        A,B=(list(map(int,next(f).split())) for _ in range(2))
    assert len(A)==len(B)==6844 and (A[-1] or B[-1])
    F=list(source())
    l1=lambda P:sum(map(abs,P))
    BN=l1(A)**2+2*l1(B)**2
    BP=prod(l1(G)**e for G,e,n,nm in F)
    DD=sum((len(G)-1)*e for G,e,n,nm in F)
    dq=13686-DD
    assert dq>0
    assert (DD,dq)==(6648,7038)
    p,n,m,Z=2**60,0,1,[0]*(dq+1)
    start=perf_counter()
    print('whole quotient streamed certificate setup',13686,DD,dq,
          BN.bit_length(),BP.bit_length(),n,flush=True)
    while n<1400:
        p=int(nextprime(p+4241))
        D=nmod_poly([1],p)
        for G,e,j,d0 in F:D*=nmod_poly([g%p for g in G],p)**e
        if D.degree()!=DD:continue
        U,V=[nmod_poly([a%p for a in W],p) for W in (A,B)]
        Q,R=divmod(U*U-2*V*V,D)
        assert not R,('full proposed exact product fails at',p,str(R)[:300])
        b=pow(m,-1,p)
        for j in range(dq+1):Z[j]+=m*((int(Q[j])-Z[j])*b%p)
        m*=p;n+=1
        if n%64==0:
            print('streamed quotient CRT',n,m.bit_length(),round(perf_counter()-start,2),flush=True)
        if m>BN:
            ql=sum(v if 2*v<m else m-v for v in Z)
            EB=BN+BP*ql
            if m>EB:
                assert Z[-1]
                print('exact norm product by streamed coefficient identity',dq,n,EB.bit_length(),
                      m.bit_length(),round(perf_counter()-start,2),flush=True)
                with gzip.open('arith67-quotient.gz','wt',encoding='utf-8') as f:
                    f.writelines(str(v if 2*v<m else v-m)+'\n' for v in Z)
                return
    raise ArithmeticError('exact product bound not yet met')

if __name__=='__main__':main()

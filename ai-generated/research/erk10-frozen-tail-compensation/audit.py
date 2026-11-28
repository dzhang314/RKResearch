#!/usr/bin/env python3
"""Independently verify exact polynomial masks and affine-family receipts."""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
import re
import sys

HERE=Path(__file__).resolve().parent
MIX=(
    ("three",('-1/6','-1/3','-1/2'),(6,11,6,1),
     ((2,1,-94),(0,2,34),(1,2,-9),(2,2,117),(3,2,-108),(0,4,-75),(0,5,36)),
     13, None,F(-96,5)),
    ("four",('1/3','-1/3','-1/2'),(-12,-4,3,1),
     ((0,2,16),(1,2,72),(3,2,-54),(0,4,-75),(0,5,36)),
     12,13,F(-384,35)),
)
REPS=(15,14,13,0,9,1,5,2,11,4)
PINS={
    'erk10-seventeen-half-port/tableau.json':
       '663c5fbfb6b303a61d30ec39830628b715f88e3349979fe0813327405bc318c4',
    'erk10-seventeen-half-port/seed6-prefix.json':
       '49e854cdda01628174223f46ba8bc9da03e1b8706b774380f7a4db9820a4f370',
}

def run(root,lean):
    for p,h in PINS.items():assert sha256((root/p).read_bytes()).hexdigest()==h
    sys.path.insert(0,str(root/'erk10-seventeen-half-port-family'))
    from check_family import factory
    (A,U,V,b),_=factory(root/'erk10-seventeen-half-port')
    c=tuple(map(sum,A))
    z=tuple(6*x for x in c)
    data=lean.read_text()
    assert all(z[i]+3==j for j,i in enumerate(REPS))
    assert b[13]==F(33,700) and c[13]==F(-1,6) and c.count(c[13])==1
    for name,rootstr,mask,poly,cut,silent,expected in MIX:
        C=defaultdict(int)
        for p,a in enumerate(mask):
            for j,k,b0 in poly:
                C[p+j,k]+=a*b0*6**(5-j-k)
        D=sorted((j,k,v)for (j,k),v in C.items()if v)
        raw=re.search(r'def '+name+r' : Fin [0-9]+ → Monomial := !\[(.*?)\]',data,re.S)
        assert raw and D==[tuple(map(int,s))for s in re.findall(r'⟨(\d+),(\d+),(-?\d+)⟩',raw[1])]
        assert all(j+k+2<=10 for j,k,_ in D)
        P=lambda x:prod(x-6*F(y)for y in rootstr)
        def load(i,q):
            v=P(z[i])*sum(sign*c[i]**j*c[q]**k for j,k,sign in poly)
            turn=sum(sign*z[i]**j*z[q]**k for j,k,sign in D)
            assert turn==6**5*v
            return v
        loadRows=[tuple(load(i,q)for q in range(17)) for i in range(17)]
        const=lambda A,i:sum(x*y for x,y in zip(A[i],loadRows[i]))
        S=tuple(const(A,i)for i in range(17))
        assert all(S[i]==S[REPS[int(z[i])+3]]for i in range(16)if i!=silent)
        assert all(const(T,i)==0 for T in (U,V)for i in range(17)if i!=silent)
        assert all(not any(loadRows[i])for i in range(cut,16)if i!=silent)
        gap=b[-1]*(S[-1]-S[REPS[int(z[-1])+3]])
        assert gap==expected
        print(name,'term count',len(D),'masked coefficient maximum total degree',max(j+k for j,k,_ in D))
        print('  literal affine-weighted missing read',gap,'kernel scaling 6^5:',6**5*gap)
        print('  frozen row count',cut,'exempt zero-weight clock',c[silent]if silent is not None else 'none')
    print('Both arrays and exact rational gates verified independently.')

if __name__=='__main__':
    p=ArgumentParser()
    p.add_argument('--research-root',type=Path,default=HERE.parent)
    p.add_argument('--lean-source',type=Path,default=HERE.parents[1]/'lean/RKCert/ReviewedNative/ERK10FrozenTailCompensation.lean')
    q=p.parse_args()
    run(q.research_root,q.lean_source)

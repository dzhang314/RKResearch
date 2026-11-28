"""Separated one-square phases and coefficient streaming bound the memory."""
import gzip,sys
from math import gcd
from pathlib import Path
from flint import fmpz_poly
from itertools import zip_longest
sys.set_int_max_str_digits(0)
def input_square(n):
    with gzip.open('literal23-oriented-exact.gz','rt',encoding='utf-8') as f:
        for _ in range(n):next(f)
        P=fmpz_poly(list(map(int,next(f).split())))
    assert P and P.degree()<=6705
    return P*P

def square():
    A=input_square(0)
    with gzip.open('lit23-square0.gz','wt',encoding='utf-8') as f:
        f.writelines(str(a)+'\n' for a in A)
    print('whole exact first square',A.degree(),flush=True)

def finish():
    B=input_square(1)
    d=-1;lead=0;c=0
    with gzip.open('lit23-square0.gz','rt',encoding='utf-8') as f, gzip.open('lit23-norm-raw.gz','wt',encoding='utf-8') as g:
        for i,(x,y) in enumerate(zip_longest(f,B,fillvalue=0)):
            z=int(x)-2*int(y)
            if z:d=i;lead=z
            c=gcd(c,z)
            g.write(str(z)+'\n')
    Path('lit23-square0.gz').unlink()
    del B
    assert d==13410 and c
    with gzip.open('lit23-norm-raw.gz','rt',encoding='utf-8') as f, gzip.open('lit23-norm-primitive.gz','wt',encoding='utf-8') as g:
        for i,line in enumerate(f):
            if i>d:break
            q,r=divmod(int(line),c);assert not r
            g.write(str(q if lead>0 else -q)+'\n')
    Path('lit23-norm-raw.gz').unlink()
    print('whole exact quadratic norm of actual orientation',d,flush=True)

from functools import lru_cache
from math import prod
from pathlib import Path
import json,sys

def require(ok,label):
    if not ok:
        raise ValueError(label)

@lru_cache(None)
def size(t):
    return 1+sum(size(u) for u in t)

@lru_cache(None)
def factorial(t):
    return size(t)*prod(factorial(u) for u in t)

@lru_cache(None)
def trees(n):
    if n==1: return ((),)
    candidates=sorted(t for j in range(1,n) for t in trees(j))
    def branch(left,lo,children):
        if left==0:
            yield children
            return
        for k in range(lo,len(candidates)):
            u=candidates[k]
            if size(u)<=left:
                yield from branch(left-size(u),k,children+(u,))
    return tuple(branch(n-1,0,()))

def verify(raw):
    p=raw['modulus'];A=raw['A'];b=raw['b'];s=len(b)
    require(p==163 and s==6 and len(A)==s and all(len(row)==s for row in A),'shape')
    require(all(A[i][j]%p==0 for i in range(s) for j in range(i+1,s)),'lower triangular')
    require(A[0][0]%p!=0 and all((A[i][i]-A[0][0])%p==0 for i in range(s)),'nonzero shared diagonal')
    @lru_cache(None)
    def phi(t):
        powers=[phi(u) for u in t]
        return tuple(prod(sum(A[i][j]*q[j] for j in range(s))%p for q in powers)%p
                     for i in range(s))
    counts=[len(trees(n)) for n in range(1,7)]
    require(counts==[1,1,2,4,9,20] and sum(counts)==37,'rooted tree counts')
    for n in range(1,7):
        for t in trees(n):
            require((factorial(t)*sum(w*u for w,u in zip(b,phi(t)))-1)%p==0,
                    repr((t,factorial(t),phi(t))))
    print(f'Verified all {sum(counts)} order conditions, literal shared diagonal {A[0][0]%p} mod {p}; per order {counts}')

if __name__=='__main__':
    verify(json.loads(Path(sys.argv[1]).read_text()))

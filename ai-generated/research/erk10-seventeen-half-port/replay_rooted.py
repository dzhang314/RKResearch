"""Exact chronological tree recurrences for the constructor."""
from scalar import *
from math import lcm

@lru_cache(None)
def trees(n,lo=(0,())):
    if not n:return ((),)
    return tuple((t,)+s for k in range(max(1,lo[0]),n+1)
                 for t in trees(k-1) if (k,t)>=lo for s in trees(n-k,(k,t)))
@lru_cache(None)
def size(t):return 1+sum(size(s)for s in t)
@lru_cache(None)
def tf(t):return size(t)*prod(tf(s)for s in t)

def audit(A,b,verbose=True):
    N=len(A)
    DD=lcm(*(x.denominator for x in (*b,*(x for r in A for x in r))))
    assert unpaid(DD)==1
    A=[tuple(int(x*DD)for x in r[:i])for i,r in enumerate(A)]
    b=tuple(int(x*DD)for x in b)
    @lru_cache(None)
    def phi(t):
        acts=[act(v)for v in t]
        return tuple(prod(q[i]for q in acts)for i in range(N))
    @lru_cache(None)
    def act(t):
        v=phi(t)
        return tuple(sum(x*y for x,y in zip(row,v))for row in A)
    def defect(t):
        return F(tf(t)*sum(x*y for x,y in zip(b,phi(t))),DD**size(t))-1
    for n, M in enumerate((1,1,2,4,9,20,48,115,286,719),1):
        ts=trees(n-1)
        assert len(ts)==M
        bad=[(t,defect(t))for t in ts if defect(t)]
        if verbose:print("conditions",n,M,"bad",len(bad),bad[:1],flush=True)
        assert not bad,(n,bad[:3])
    gaps=[];g=0
    for t in trees(10):
        d=defect(t);G=gcd(g,d.numerator)
        if d and G!=g:
            gaps.append((t,d));g=G
            if unpaid(g)==1:break
    assert unpaid(g)==1
    if verbose:print('common denominator',DD,'next defects',gaps,'gcd',g,flush=True)
    return DD,gaps

"""Rooted trees as sorted child tuples; no normalized-profile cache."""
from functools import cache
from math import prod

@cache
def trees(n):
    smaller=[(k,t)for k in range(1,n)for t in trees(k)]
    def children(left,lo):
        if not left:
            yield ()
        for i in range(lo,len(smaller)):
            k,t=smaller[i]
            if k>left:
                break
            for rest in children(left-k,i):
                yield (t,*rest)
    return tuple(children(n-1,0))

@cache
def order(t):
    return 1+sum(order(u) for u in t)

@cache
def tf(t):
    return order(t)*prod(tf(u) for u in t)

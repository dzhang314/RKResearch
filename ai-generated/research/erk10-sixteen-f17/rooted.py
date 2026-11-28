"""Enumerate ordinary rooted trees in increasing grade."""
from functools import cache
from math import prod

@cache
def trees(n):
    if n==1:return ((),)
    smaller=[(k,t)for k in range(1,n)for t in trees(k)]
    def walks(k,j):
      if k==0:yield ()
      for i in range(j,len(smaller)):
        s,t=smaller[i]
        if s>k:break
        for c in walks(k-s,i):yield (t,*c)
    return tuple(walks(n-1,0))
@cache
def size(t):return 1+sum(map(size,t))
@cache
def tf(t):return size(t)*prod(map(tf,t))

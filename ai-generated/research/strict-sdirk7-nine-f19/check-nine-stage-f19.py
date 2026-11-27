"""Independent finite rooted checks for the literal nine-stage F19 tableau."""
import json
from math import prod
from functools import cache
from pathlib import Path

p=19
s=json.loads(Path(__file__).with_name("nine-stage-f19.json").read_text())
A,b=s["A"],s["b"]
assert len(A)==len(b)==9 and all(len(row)==9 for row in A)
assert all(row[i]==8 and not any(row[i+1:]) for i,row in enumerate(A))
assert [sum(row)%p for row in A]==[8,6,0,2,3,9,10,11,12]
assert pow(8,-1,19)==12

# Encode an unordered rooted tree canonically by a sorted tuple of subtrees.
# Generate all multisets of smaller trees whose total size is the target.
layers=[[],[()]]
pool=[(1,())]
for n in range(2,8):
    def multiset(size,first=0):
        if not size:
            yield ()
        else:
            for i,(a,ch) in enumerate(pool):
                if i<first:continue
                if a>size:break
                for t in multiset(size-a,i):
                    yield (ch,)+t
    ls=list(multiset(n-1))
    layers.append(ls)
    pool.extend((n,x) for x in ls)

assert [len(layer) for layer in layers[1:]]==[1,1,2,4,9,20,48]

@cache
def sz(t):
    return 1+sum(map(sz,t))

@cache
def fact(t):
    return sz(t)*prod(map(fact,t))

@cache
def elementary(t):
    result=[1]*9
    for child in t:
        prev=elementary(child)
        for i in range(9):
            result[i]=(result[i]*sum(A[i][j]*prev[j] for j in range(i+1)))%p
    return result

def receipt(t):
    return fact(t)*sum(w*y for w,y in zip(b,elementary(t)))%p

assert all(receipt(t)==1 for ls in layers for t in ls)
assert receipt(((),)*7)==12!=1
print("Verified all 85 rooted conditions over F19. Eighth bush = 12, so the order is exactly seven.")

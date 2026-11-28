from pathlib import Path
from functools import cache
from itertools import combinations_with_replacement
from math import prod
import json
@cache
def trees(n):
    if n==1:
        return ((),)
    bucket=[(k,t) for k in range(1,n) for t in trees(k)]
    def fill(start,left):
        if left==0:
            yield ()
        else:
            for i in range(start,len(bucket)):
                k,t=bucket[i]
                if k>left:break
                for r in fill(i,left-k):yield (t,)+r
    return tuple(fill(0,n-1))
@cache
def size(t): return 1+sum(map(size,t))
@cache
def factorial(t): return size(t)*prod(map(factorial,t))
def verify(path):
    j=json.loads(path.read_text())
    q=int(j.get('modulus',j.get('field')))
    a=[list(map(int,row)) for row in j['A']]
    b=list(map(int,j['b']))
    assert len(a)==len(b)==16 and all(len(row)==i for i,row in enumerate(a))
    @cache
    def stage(t):
        return tuple(prod(advance(s)[i] for s in t)%q for i in range(16))
    @cache
    def advance(t):
        v=stage(t)
        return tuple(sum(x*v[k] for k,x in enumerate(row))%q for row in a)
    def residual(t):
        return (factorial(t)*sum(x*y for x,y in zip(b,stage(t)))-1)%q
    t=tuple(() for _ in range(10)); defects=[residual(s) for n in range(1,11) for s in trees(n)]
    assert len(defects)==1205 and not any(defects)
    assert residual(t) == j["bush_failure"] and residual(t) % j["prime"]
    print(path.name,q,len(defects),residual(t))

if __name__=='__main__':
    from sys import argv
    source = Path(argv[1])
    seeds = json.loads((Path(__file__).parent/'seeds.json').read_text())
    seen = set(source.glob('mod*pow*.json'))
    for p, *_ in seeds:
        last = None
        e = 1
        while (path := source/f'mod{p}pow{e}.json') in seen:
            j = json.loads(path.read_text())
            assert j['modulus']==p**e and j['prime']==p and j['exponent']==e
            if last is not None:
                m = last['modulus']
                assert [i%m for i in j['b']]==last['b']
                assert [[i%m for i in row] for row in j['A']]==last['A']
            last = j
            verify(path)
            seen.remove(path)
            e += 1
        assert e > 2
    assert not seen

"""Independent exact verification of every unordered rooted tree through seven."""
from fractions import Fraction as F
from functools import cache
from math import prod
from pathlib import Path
import json

@cache
def size(t):
    return 1+sum(map(size,t))

@cache
def tree_factorial(t):
    return size(t)*prod(map(tree_factorial,t))

def enumerate_trees(limit):
    layers = [[()]]
    for n in range(2,limit+1):
        children = [t for group in layers for t in group]

        def forests(start,left):
            if left == 0:
                yield ()
                return
            for j in range(start,len(children)):
                child = children[j]
                if size(child)>left:
                    break
                for tail in forests(j,left-size(child)):
                    yield (child,)+tail

        layers.append(list(forests(0,n-1)))
    return layers

def replay(s):
    d,e,A,b = (s[k] for k in ('stage_den','weight_den','A','b'))
    assert d==2**15*3**3*5 and e==2**3*3**3*5*7**2
    assert 5040**4 % d == 5040**4 % e == 0
    assert len(A)==len(b)==10 and all(len(row)==10 for row in A)
    assert all(4*row[i]==d and not any(row[i+1:]) for i,row in enumerate(A))
    assert [4*sum(r) for r in A] == [d*x for x in
                                      [1,6,0]+s['normalized_tail_clocks']]

    @cache
    def stage(t):
        x = (1,)*10
        for child in t:
            v = stage(child)
            x = tuple(u*sum(a*w for a,w in zip(row,v)) for u,row in zip(x,A))
        return x

    def payment(t):
        return F(tree_factorial(t)*sum(x*w for x,w in zip(stage(t),b)),e*d**(size(t)-1))

    layers = enumerate_trees(8)
    assert list(map(len,layers)) == [1,1,2,4,9,20,48,115]
    assert all(payment(t)==1 for layer in layers[:7] for t in layer)
    assert payment(((),)*7)==1
    treeA = (((), ((),(),(),())),)
    treeB = (((((),(),(),()),),),)
    assert size(treeA)==size(treeB)==8
    assert [payment(treeA),payment(treeB)] == [F(631,576),F(-5,96)]
    assert 6*101-11*55==1
    assert not any(5040**4 % j for j in (576,96))
    assert [payment(layers[7][r['index']]) for r in s['order_eight_failures']] ==         [F(r['payment']) for r in s['order_eight_failures']]
    print('85/85 rooted order conditions; eighth-order failures 631/576 and -5/96.')
    print('Only paid denominators, and Bezout exactness under every allowed coefficient map.')

if __name__=='__main__':
    replay(json.loads(Path(__file__).with_name('ten-stage-paid.json').read_text()))

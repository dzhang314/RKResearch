#!/usr/bin/env python3
"""Exact, independent F17 weights and two observed rooted pairings."""
from itertools import combinations
from math import prod
p=17
I=lambda n:pow(n+1,-1,p)
g=10
r0=g*g*I(1)%p
assert (12*g)%p==1 and r0==16
Z=[10,9,8]
W=[5,8,5]
assert len(set(Z))==3 and all((5*(2*x-1)**3-3*(2*x-1))%p==0 for x in Z)
I0=lambda j:(I(j)-sum(w*x**j for w,x in zip(W,Z)))%p
assert all(I0(j)==0 for j in range(6))
assert I0(6)==pow(2800,-1,p) and I0(7)==7*I(1)*I0(6)%p
external=[g,3*g%p,5*g%p, (1-5*g)%p,(1-3*g)%p,(1-g)%p]
assert external==[10,13,16,2,5,8] and sum(external)%p==3
h=(I0(7)*pow(I0(6),-1,p)-sum(external))%p
assert h==9
sites=external+[h]
assert len(set(sites))==7
def poly(xs):
    coeff=[1]
    for x in xs:
        coeff=[-x*coeff[0]]+[a-x*b for a,b in zip(coeff,coeff[1:])]+[coeff[-1]]
    return coeff
def cardinal(x):
    rest=[y for y in sites if y!=x]
    return (sum(a*I0(j) for j,a in enumerate(poly(rest)))*pow(prod(x-y for y in rest),-1,p))%p
weights={x:cardinal(x) for x in sites}
assert [weights[x] for x in sites]==[15,11,2,2,11,15,12]
for pos in range(4):
    middle=[(x,0,w) for x,w in zip(Z,W)]
    middle.insert(pos,(h,r0,weights[h]))
    off=lambda xs:[(x,r0,weights[x]) for x in xs]
    data=off(external[:3])+middle+off(external[3:])
    cs,gs,bs=map(list,zip(*data))
    assert all(sum(w*x**j for x,k,w in data)%p==I(j) for j in range(8))
    assert all(sum(w*k*x**j for x,k,w in data)%p==0 for j in range(6))
    if pos<2:
        mask=[w*(8+4*x+2*x*x+x**3+k*(3+6*x))%p for x,k,w in data]
        assert mask==[10,12,16]+([13,1] if pos==0 else [1,13])+[0]*5
        # The zero tap into an immediately following off-zero row is forced by Av=Cv.
        reads=[(-x*x*I(1)-k+(g*x if k==0 else 0))%p for x,k,w in data[:5]]
        assert reads==[2,10,9]+([3,16] if pos==0 else [16,3])
        lhs=sum(w*r for w,r in zip(mask,reads))%p
        assert lhs==16
        print('extra off-zero row',pos+4,'masked A(Cg) read',lhs,'required',0)
    else:
        mask=[w*(x+9)*(1+k)%p for x,k,w in data]
        assert mask==[0,0,0,10,8,0,0,0,0,0]
        q=lambda x:6+12*x+5*x*x
        j=lambda x:6*x+12*x*x*I(1)+5*x**3*I(2)
        assert all((q(x)-x**3)%p==0 for x in cs[:3])
        reads=[j(10)%p,(j(9)+g*(9**3-q(9)))%p]
        assert reads==[9,13]
        lhs=sum(w*r for w,r in zip(mask[3:5],reads))%p
        rhs=(I(3)*(I(5)+9*I(4)))%p
        assert (lhs,rhs)==(7,8)
        print('extra off-zero row',pos+4,'masked A(c^3) read',lhs,'required',rhs)

#!/usr/bin/env python3
"""Order-eight certificates for Cooper-Verner and the unsplit Shanks tableau.

The exact inputs are the mathematical coefficients (not program source).
Pairs (a,b) denote a+b*S, S^2=21, with rational a,b.
"""
from fractions import Fraction as F
from math import prod


class Q:
    __slots__ = ('a','b')
    def __init__(self, a=0, b=0):
        self.a = F(a)
        self.b = F(b)
    def __add__(self, y):
        if not isinstance(y, Q): y = Q(y)
        return Q(self.a+y.a, self.b+y.b)
    __radd__ = __add__
    def __mul__(self, y):
        if not isinstance(y, Q): y = Q(y)
        return Q(self.a*y.a+21*self.b*y.b, self.a*y.b+self.b*y.a)
    __rmul__ = __mul__
    def __eq__(self, y):
        if not isinstance(y, Q): y=Q(y)
        return self.a==y.a and self.b==y.b
    def at(self, n, s):
        assert (s*s-21)%n==0
        return (self.a.numerator*pow(self.a.denominator,-1,n)+s*self.b.numerator*pow(self.b.denominator,-1,n))%n


# One token per strict predecessor, rational coefficients separated by comma.
# Based on Cooper & Verner (1972), doi:10.1137/0709037, rkcv8 chart.
CVrows = [
'',
'1/2',
'1/4 1/4',
'1/7 -1/14,3/98 3/7,-5/49',
'11/84,-1/84 0 2/7,-4/63 1/12,1/252',
'5/48,-1/48 0 1/4,-1/36 -77/120,-7/180 63/80,7/80',
'5/21,1/42 0 -48/35,-92/315 211/30,29/18 -36/5,-23/14 9/5,13/35',
'1/14 0 0 0 1/9,1/42 13/63,1/21 1/9',
'1/32 0 0 0 91/576,7/192 11/72 -385/1152,25/384 63/128,-13/128',
'1/14 0 0 0 1/9 -733/2205,1/15 515/504,-37/168 -51/56,11/56 132/245,-4/35',
'0 0 0 0 -7/3,-7/18 -2/5,-28/45 -91/24,53/72 301/72,-53/72 28/45,28/45 49/18,7/18',
]
CVweights = '1/20 0 0 0 0 0 0 49/180 16/45 49/180 1/20'
def readQ(row): return tuple(Q(*a.split(',')) for a in row.split())

# Independent construction of all unlabeled rooted, non-plane trees.
# Each tree has its list of earlier child indices in nondecreasing order.
def trees_upto(p):
    T=[]; sizes=[]; gamma=[]
    def forests(k,left):
        if left==0:
            yield ()
        else:
            for i in range(k,len(sizes)):
                if sizes[i]>left: break
                for tail in forests(i,left-sizes[i]):
                    yield (i,)+tail
    for d in range(1,p+1):
        trees=list(forests(0,d-1))
        for t in trees:
            T.append(t); sizes.append(d); gamma.append(d*prod(gamma[i] for i in t))
    return T,sizes,gamma

def evaluate(A,b,m=0):
    T,s,g=trees_upto(9)
    def red(x): return x%m if m else x
    assert len(A)==len(b) and all(len(row)==i for i,row in enumerate(A))
    stages=[]; feeds=[]; defects=[]
    for t,j,k in zip(T,s,g):
        phi=[red(prod(feeds[ch][i] for ch in t)) for i in range(len(A))]
        stages.append(phi)
        feeds.append([red(sum(x*y for x,y in zip(row,phi))) for row in A])
        defects.append(red(k*sum(x*y for x,y in zip(b,phi)) + (-1)))
    assert [s.count(j) for j in range(1,10)]==[1,1,2,4,9,20,48,115,286]
    assert all(d==0 for d,sz in zip(defects,s) if sz<=8)
    bush=T.index((0,)*8)
    return defects[bush]

def remove_factors(n,primes):
    for p in primes:
        while n%p==0: n//=p
    return n

def shrow(q,*xs):return tuple(F(x,q) for x in xs)
AS=((),shrow(9,1),shrow(24,1,3),shrow(16,1,0,3),shrow(500,29,0,33,-12),shrow(972,33,0,0,4,125),shrow(36,-21,0,0,76,125,-162),shrow(243,-30,0,0,-32,125,0,99),shrow(324,1175,0,0,-3456,-6250,8424,242,-27),shrow(324,293,0,0,-852,-1375,1836,-118,162,324),shrow(1620,1303,0,0,-4260,-6875,9990,1030,0,0,162),shrow(4428,-8595,0,0,30720,48750,-66096,378,-729,-1944,-1296,3240))
bS=shrow(840,41,0,0,0,0,216,272,27,27,36,180,41)

def main():
    A=tuple(map(readQ,CVrows)); b=readQ(CVweights)
    for a in (a for row in (*A,b) for a in row):
        assert all(remove_factors(c.denominator,[2,3,5,7])==1 for c in (a.a,a.b))
    d=evaluate(A,b)
    print(f'Cooper-Verner: 200 rooted conditions over Z[1/210,S]/(S²-21); order-9 bush defect {d.a}+({d.b}) S')
    assert d.b==0 and d.a==F(1,3920)
    print('CV numeric tableau at S=12 over F_41:')
    modA=[tuple(a.at(41,12) for a in r) for r in A]
    modb=tuple(a.at(41,12) for a in b)
    print('A =',modA); print('b =',modb)
    d41=evaluate(modA,modb,41)
    print('F_41: 200 rooted conditions; order-9 bush defect:',d41)
    assert d41==d.at(41,12)==23
    for row in (*AS,bS):
        assert all(remove_factors(x.denominator,[2,3,5,7,41])==1 for x in row)
    dS=evaluate(AS,bS)
    print('Shanks: 200 rooted conditions over Z[1/8610]; order-9 bush defect:',dS)
    assert dS==F(1,4320)

if __name__=='__main__': main()

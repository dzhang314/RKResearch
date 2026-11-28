from fractions import Fraction as Q
from itertools import permutations

L3=(-1,12,-30,20)
L4=(1,-20,90,-140,70)
L5=(-1,30,-210,560,-630,252)
I=lambda c,j:sum(Q(v,i+j+1) for i,v in enumerate(c))
for d,P in enumerate((L3,L4,L5),3):
    assert len(P)==d+1 and P[-1]
    assert all(I(P,j)==0 for j in range(d))
    assert I(P,d)!=0

def det(a):
    r=Q(0)
    for p in permutations(range(len(a))):
        z=Q((-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p))))
        for i,j in enumerate(p):
            z*=a[i][j]
        r+=z
    return r

for n in (3,4):
    assert det([[Q(1,i+j+1) for j in range(n)] for i in range(n)])
print("three shifted Legendre profiles and both paid scalar moment pivots verified")

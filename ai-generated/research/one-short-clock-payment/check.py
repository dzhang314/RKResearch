from fractions import Fraction as Q
from itertools import product
from math import prod

def matrix(n, entries):
    return [[Q(entries.get((i + 1, j + 1), 0)) for j in range(n)] for i in range(n)]

def check(name, b, entries, n, expected, order):
    b = list(map(Q, b))
    A = matrix(len(b), entries)
    c = list(map(sum, A))
    assert all(A[i][j] == 0 for i in range(len(b)) for j in range(i, len(b)))
    assert sum(b) == 1 and sum(x*y for x, y in zip(b, c)) == Q(1, 2)
    if order == 3:
        assert sum(x*y**2 for x, y in zip(b, c)) == Q(1, 3)
        assert sum(b[i]*A[i][j]*c[j] for i,j in product(range(len(b)), repeat=2)) == Q(1,6)
    assert sum(x*y**order for x,y in zip(b,c)) != Q(1,order+1)
    sites = sorted(set(c))
    B = {t:sum(x for x,y in zip(b,c) if y==t) for t in sites}
    M = {(u,v):sum(b[i]*A[i][j] for i,j in product(range(len(b)), repeat=2)
             if c[i]==u and c[j]==v) for u,v in product(sites, repeat=2)}
    D = {(u,v):M[u,v]+M[v,u]-B[u]*B[v] for u,v in product(sites, repeat=2)}
    def S(f,g):
        return sum(D[u,v]*f(u)*g(v) for u,v in product(sites,repeat=2))
    for i in range(order-1):
        for j in range(order-1-i):
            assert S(lambda x:x**i,lambda x:x**j)==0
    T = sorted(t for t in sites if B[t])
    assert len(T)==n
    corrected, physical, leakage = [], [], []
    for t in T:
        s = lambda x: int(x==t)
        q = lambda x: prod(x-y for y in T if y!=t)
        k = q(t)
        h = lambda x: q(x)-k*s(x)
        J = 2*k*S(s,h)+S(h,h)
        corrected.append(S(q,q))
        physical.append(k*k*D[t,t])
        leakage.append(J)
        assert physical[-1]+J==corrected[-1]
    if 2*n<=order+1: assert len(set(corrected))==1
    if name=="signed4":
        assert S(lambda x:x==T[0],lambda x:x not in T)==1
        assert S(lambda x:x not in T,lambda x:x not in T)==-2
    assert (physical,leakage,corrected)==expected
    print(f"{name}: exact order {order}, closure {list(map(str,T))}; "
          f"scaled physical {list(map(str,physical))}; leakage {list(map(str,leakage))}; "
          f"corrected {list(map(str,corrected))}")

check("signed4",[-1,0,1,1],{(2,1):Q(1,2),(3,2):Q(1,2),(4,1):-1,(4,2):1},
      1,([0],[0],[0]),2)
check("heun3",[Q(1,4),0,Q(3,4)],{(2,1):Q(1,3),(3,2):Q(2,3)},2,
      ([Q(-1,36),Q(-1,4)],[0,Q(2,9)],[Q(-1,36)]*2),3)
check("joint5",[0,0,0,Q(1,4),Q(3,4)],
      {(2,1):Q(1,3),(3,1):Q(2,3),(4,1):1,(4,2):-2,(4,3):1,
       (5,1):Q(2,3),(5,2):Q(-2,3),(5,3):Q(2,3)},2,
      ([Q(7,36)]*2,[Q(-2,9)]*2,[Q(-1,36)]*2),3)

# A direct four-stage ERK3 with only the two left-Radau clocks (no hidden
# stages at all). Row 2 sets the donor clock 2/3; row 3 is another 0 row.
check("radau4",[0,0,Q(1,4),Q(3,4)],
      {(2,1):Q(2,3),(4,1):Q(1,3),(4,2):Q(1,3)},2,
      ([Q(-1,36)]*2,[0,0],[Q(-1,36)]*2),3)

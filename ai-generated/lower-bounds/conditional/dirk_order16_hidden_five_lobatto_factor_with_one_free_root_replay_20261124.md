# Exact replay: a Lobatto factor times one unknown affine factor cannot have the first two primitive moments zero at an omitted node

Companion of dirk_order16_every_twenty_two_stage_method_has_a_hidden_fifth_grade_pure_20261124.md. The monic Q of degree at most four is an arbitrary divisor of D=x(x-1)L8′ scaled to be monic; u is a nonzero grid root with Q(u) nonzero. The two-by-two Hankel matrix for I_u[x Q], I_u[x² Q], I_u[x³ Q] has nonzero determinant. Nothing is asserted for Q that do not divide this fixed D. Each prime below suffices independently. No unknown tableau coefficients or free affine root are reduced. The polynomial D is squarefree with nine distinct roots modulo each prime, all denominators of the moment tests are units; every embedding of its algebraic splitting field can be reduced at a prime over the chosen prime after inverting the leading coefficient. Any exact zero would reduce to a zero among the enumerated choices.

Fresh exact Python output:
~~~text
1979 [0, 1, 610, 921, 946, 990, 1034, 1059, 1370] [8, 64, 224, 448, 560] all determinants nonzero
2909 [0, 1, 395, 707, 1320, 1455, 1590, 2203, 2515] [8, 64, 224, 448, 560] all determinants nonzero
~~~

Complete standalone Python 3:
~~~python
from itertools import combinations
from math import comb,isqrt
def poly(q,u,p):
    a=0
    for v in q[::-1]: a=(a*u+v)%p
    return a
def factor(S,p):
    q=[1]
    for t in S: q=[((q[i-1] if i else 0)-t*(q[i] if i<len(q) else 0))%p for i in range(len(q)+1)]
    return q
def run(p):
    assert p>17 and all(p%t for t in range(2,isqrt(p)+1))
    L=[(-1)**(8-j)*comb(8,j)*comb(8+j,j) for j in range(9)]
    dL=[j*L[j] for j in range(1,9)]
    G=[0,1]+[u for u in range(p) if poly(dL,u,p)==0]
    assert dL[-1]%p and len(set(G))==len(G)==9
    def I(q,u,j): return sum(a*pow(u,j+i+1,p)*pow(j+i+1,-1,p) for i,a in enumerate(q))%p
    X=[[],[],[],[],[]];tests=[0]*5
    for n in range(5):
        for S in combinations(G,n):
            q=factor(S,p)
            for u in G[1:]:
                if u in S: continue
                A,B,C=(I(q,u,j) for j in (1,2,3))
                tests[n]+=1
                if (A*C-B*B)%p==0:X[n].append((S,u))
    assert tests==[8,64,224,448,560] and not any(X), X
    print(p,G,tests,'all determinants nonzero')
for p in (1979,2909):run(p)
~~~

I also reran the upstream two-pivot certificate at 1033 and 1237, obtaining identical rank-pair counts (5,6):144, (4,6):7, (6,6):2985, zero bad. The three-pivot affine-leakage replay passed all six (m,p) inputs, with unresolved first-pair counts 0,0,8,8,247,245; individual third-pair rank tests 0,0,392,392,15808,15680. As in its source, the p18 and p20 geometric applications are conditional on their leakage hypotheses. The older hidden-six primary is dated 20261123, not 20261124.

"""Exact singleton-zero scalar checks in integers and in the prime field F_17.

The quartic reduction is a specialization of the characteristic-zero
coefficient ring, not an assertion about actual RK methods over F_17.
"""
from itertools import permutations

def clean(P, mod):
    P = tuple(a % mod if mod is not None else a for a in P)
    n = len(P)
    while n and P[n-1] == 0:
        n -= 1
    return P[:n]

def add(*ps, mod=None):
    return clean((sum(P[j] for P in ps if j < len(P))
                  for j in range(max(map(len,ps),default=0))), mod)

def scale(c, P, mod=None):
    return clean((c*x for x in P),mod)

def mul(*ps, mod=None):
    res=(1,)
    for P in ps:
        co = [0]*max(0,len(res)+len(P)-1)
        for i,a in enumerate(res):
            for j,b in enumerate(P):
                co[i+j] += a*b
        res=clean(co,mod)
    return res

def power(P,n,mod=None):
    return mul(*([P]*n),mod=mod)

kap=(1,2,-1)
H=(-2,1,4,-1)

def Q3(p,d1,d2,d3):
    return (4*d1-2*d2-6*p,-8*d1+5*d2-6*d3+15*p,
            3*d1-4*d2+7*d3-10*p,2*(d2+2*d3+p))

def K2(p,d1,d2,d3):
    return d1-2*p,d2+p,d3

# The uneliminated arithmetic gate is linear in the four Taylor coefficients.
# Checking all four integer coordinate columns checks the formal factorization.
for i in range(4):
    jes=tuple(int(j==i) for j in range(4))
    p,d1,d2,d3=jes
    P2u=(p,2*d1,4*d2,8*d3)
    kap2u=(1,4,-4)
    mixed=add(mul(H,kap2u),(0,0,-8,12))
    raw=add(mul(H,P2u,kap), scale(-1,mul(mixed,add(scale(p,kap),mul((0,2),K2(*jes))))))
    assert raw==mul((0,0,2),kap,Q3(*jes))

MOD=17
def inv(x):
    return pow(x,-1,MOD)

def determinant(M):
    s=()
    n=len(M)
    for p in permutations(range(n)):
        sg=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        s=add(s,scale(sg,mul(*(M[i][p[i]] for i in range(n)),mod=MOD),mod=MOD),mod=MOD)
    return s

def sylvester(P, Q): # ascending in elimination variable; coefficient polys in h
    n,m=len(P)-1,len(Q)-1
    return determinant([[()] * i + list(reversed(P)) + [()]*(m-1-i)
                         for i in range(m)]
                        + [[()] * i + list(reversed(Q)) + [()]*(n-1-i)
                           for i in range(n)])

def front(a):
    assert (70*a**4-140*a**3+90*a*a-20*a+1)%MOD==0
    g=(4+35*a*(1-a))*inv(72)%MOD
    c0=(a**3-2*a*a+9*inv(7)*a-2*inv(7))%MOD
    c1=(a*a-2*a+9*inv(7))%MOD
    c2=(a-2)%MOD
    p=(g**3+c2*g*g+c1*g+c0)%MOD
    d1=g*(3*g*g+2*c2*g+c1)%MOD
    d2=g*g*(3*g+c2)%MOD
    d3=g**3%MOD
    D=(d2+2*d3+p)%MOD
    assert g and p and D
    P=tuple((x%MOD,) for x in Q3(p,d1,d2,d3))
    Q=tuple((x%MOD,-p*k%MOD) for x,k in zip(K2(p,d1,d2,d3),kap))
    f=sylvester(P,Q)
    assert len(f)==4 # no cancellation of the cubic degree
    return g,(p,d1,d2,d3,D),P,f

g,jet,P,F=front(7)
gg,rjet,RP,R=front(11)  # 1-7 mod 17
assert g==gg==16
L=(inv(g)-2)%MOD
assert L==14
assert jet==(15,12,2,16,15)
assert rjet==(10,7,6,16,14)
assert P==((5,),(9,),(7,),(13,))
assert RP==((7,),(11,),(9,),(11,))
assert F==(-3%MOD,-3%MOD,6,7)
assert R==(1,6,-6%MOD,-4%MOD)
V=add(*(scale(c,mul(power((0,-1),i,MOD),power((1,L),3-i,MOD),mod=MOD),mod=MOD)
        for i,c in enumerate(R)),mod=MOD)
assert V==(1,2,6,-8%MOD)
assert add(mul((-6,7,-6),F,mod=MOD),mul((0,3,-1),V,mod=MOD),mod=MOD)==(1,)
res=sylvester(tuple((c,) for c in F),tuple((c,) for c in V))
assert len(res)==1 and res[0]!=0
print("singleton SDIRK8 arithmetic factor checked coefficientwise")
print("F17 specialization a=7, reflect=11, gamma=16, L=14")
print("ascending F_front, F_reflected, transformed:", F,R,V)
print("exact modular Bezout identity = 1; final Sylvester determinant =",res[0])

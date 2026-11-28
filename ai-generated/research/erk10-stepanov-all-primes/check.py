"""Exact exceptional-prime audit for the archived Stepanov ERK10 coefficients."""
from fractions import Fraction
from functools import cache
from hashlib import sha256
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import json
import sys

source = Path(sys.argv[1]).read_bytes()
assert sha256(source).hexdigest() == "72b63e2ea2aaf3a4cf340e65d2ebc8f56e34accce5f36026543260c398ca869f"
inputs = json.loads(Path(sys.argv[2]).read_text())
facts = {int(p):int(k) for p,k in inputs["factors"]}
seeds = {int(p):(int(x),int(y),int(z)) for p,x,y,z in inputs["seeds"]}
assert len(facts) == 21 and len(seeds) == 61

@cache
def prove_prime(n):
    if n < 100000:
        assert n > 1 and all(n % q for q in range(2,isqrt(n)+1))
        return
    from sympy import factorint
    fs = {int(q):int(k) for q,k in factorint(n-1).items()}
    assert prod(q**k for q,k in fs.items()) == n-1
    for q in fs:
        prove_prime(q)
    for a in range(2,1000):
        if pow(a,n-1,n)==1 and all(gcd(pow(a,(n-1)//q,n)-1,n)==1 for q in fs):
            return
    raise AssertionError(f"no Lucas witness for {n}")

for p in set(seeds)|set(facts):
    prove_prime(p)

raw = [list(map(int,line.split())) for line in source.splitlines()]
assert len(raw)==135 and all(len(r)==9 and r[-1]>0 for r in raw)
coeff=[]
for a,b,c,d,e,f,g,h,w in raw:
    coeff.append(tuple(Fraction(k,63*w) for k in (63*a,63*b,63*c,63*d,3*e,-2*f+7*h,3*g,f-2*h)))
D=lcm(*(v.denominator for row in coeff for v in row))
assert D == prod(p**e for p,e in facts.items())
num=[tuple(int(v*D) for v in row) for row in coeff]
assert set(p for p in facts if p>7) == ({523}|(set(seeds)&set(facts)-{2,3,5,7}))
print(f"Prime-tested complete denominator factorization: {len(facts)} primes, 17 above 7")
print(f"D = {D}")

def square_root_lift(x, a, p, digits):
    m=p
    assert (x*x-a)%p==0 and (2*x)%p!=0
    for _ in range(1,digits):
        q,r=divmod(x*x-a,m)
        assert r==0
        x+=m*(-q*pow(2*x,-1,p)%p)
        m*=p
    assert (x*x-a)%m==0
    return x%m

def transfer(vals,p):
    e=facts.get(p,0)
    pe=p**e
    assert all(u%pe==0 for row in vals for u in row)
    return [tuple(u//pe * pow(D//pe,-1,p*p)%(p*p) for u in row) for row in vals]

def scalar_rows(p, seed):
    x,y,z=seed
    digits=facts.get(p,0)+2
    m=p**digits
    x=square_root_lift(x,3,p,digits)
    y=square_root_lift(y,7,p,digits)
    z=square_root_lift(z,147+42*y,p,digits)
    basis=(1,x,y,x*y,z,x*z,y*z,x*y*z)
    return transfer([(sum(a*b for a,b in zip(row,basis))%m,) for row in num],p)

def quadratic_rows():
    p=523; digits=facts[p]+2; m=p**digits
    assert pow(3,(p-1)//2,p)==p-1
    y=square_root_lift(141,7,p,digits)
    u=square_root_lift(218,(147+42*y)*pow(3,-1,m)%m,p,digits)
    # Work in the rank-two ring on x^2=3, with z=ux.
    basis=((1,0),(0,1),(y,0),(0,y),(0,u),(3*u,0),(0,u*y),(3*u*y,0))
    vals=[tuple(sum(a*b[j] for a,b in zip(row,basis))%m for j in (0,1)) for row in num]
    return transfer(vals,p)

@cache
def trees(n):
    return forests(n-1,())

@cache
def grade(t):
    return 1+sum(map(grade,t))

@cache
def forests(n,u):
    if n==0:
        return ((),)
    return tuple((t,)+f for j in range(grade(u),n+1) for t in trees(j)
                 if j>grade(u) or t>=u for f in forests(n-j,t))

@cache
def density(t):
    return grade(t)*prod(map(density,t))

def rooted_orders(rows,m):
    quad=len(rows[0])==2
    if quad:
        zero,one=(0,0),(1,0)
        def plus(x,y):
            return ((x[0]+y[0])%m,(x[1]+y[1])%m)
        def times(x,y):
            return ((x[0]*y[0]+3*x[1]*y[1])%m,(x[0]*y[1]+x[1]*y[0])%m)
        def scale(k,x):
            return tuple(k*c%m for c in x)
        rows=[tuple(c%m for c in x) for x in rows]
    else:
        zero,one=0,1
        def plus(x,y): return (x+y)%m
        def times(x,y): return x*y%m
        def scale(k,x): return k*x%m
        rows=[x[0]%m for x in rows]

    c,b=rows[:15],rows[15:30]
    A=[rows[30+i*(i-1)//2:30+i*(i+1)//2] for i in range(15)]
    assert all(len(row)==i for i,row in enumerate(A))
    def dot(x,y):
        r=zero
        for a,b in zip(x,y):
            r=plus(r,times(a,b))
        return r
    assert [dot(row,[one]*15) for row in A]==c

    @cache
    def stage(t):
        out=[one]*15
        for u in t:
            w=read(u)
            out=[times(x,y) for x,y in zip(out,w)]
        return tuple(out)

    @cache
    def read(t):
        return tuple(dot(row,stage(t)) for row in A)

    counts=[len(trees(k)) for k in range(1,11)]
    assert counts==[1,1,2,4,9,20,48,115,286,719]
    for k in range(1,11):
        for t in trees(k):
            assert scale(density(t),dot(b,stage(t)))==one,(m,k)
    residual=plus(scale(11,dot(b,stage(((),)*10))),scale(-1,one))
    expected=pow(52920,-1,m)
    assert residual == ((expected,0) if quad else expected)
    return expected

for p,seed in sorted(seeds.items()):
    rows=scalar_rows(p,seed)
    print(f"{p}: prime-field and square verified, defect {rooted_orders(rows,p)}/{rooted_orders(rows,p*p)}")
rows=quadratic_rows()
assert rooted_orders(rows,523)==399 and rooted_orders(rows,523**2)==50607
print("523: quadratic field and square verified, defect 399/50607")
print("124 distinct literals checked: all 1205 rooted conditions plus unit bush at each")

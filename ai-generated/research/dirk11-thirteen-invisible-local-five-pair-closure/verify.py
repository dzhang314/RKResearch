"""Independent exact arithmetic for the no-slack transfer, not HasOrder."""
from collections import Counter
from fractions import Fraction as Q
import sympy as S

J4 = [1, -14, 56, -84, 42]
Y = S.Symbol("Y")
j4 = sum(a*Y**i for i, a in enumerate(J4))
j5 = (2*Y-1)*(66*Y**4-132*Y**3+84*Y**2-18*Y+1)
fiber_moment = lambda i: Q(1, (i+2)*(i+3))
assert [sum(a*fiber_moment(i+k) for i,a in enumerate(J4)) for k in range(5)] == [0,0,0,0,Q(1,13860)]
assert S.Poly(j5, Y).LC() == 132
assert all(S.integrate(Y**k*Y*(1-Y)*j5, (Y,0,1)) == 0 for k in range(4))
assert S.gcd(j4,j5) == 1
gram = S.Matrix([[fiber_moment(i+j) for j in range(4)] for i in range(4)])
assert gram.det() != 0
print("Exact anchored Jacobi basis; H cardinal scalar -1/13860", flush=True)

u,v=S.symbols("u v")
A=Y*(Y-u)*(Y-v)
assert S.expand(S.integrate(A,(Y,0,u))-u**3*(2*v-u)/12)==0
assert S.expand(S.integrate(Y*A,(Y,0,u))-u**4*(5*v-3*u)/60)==0
b0,b1,g,k0,k1=S.symbols("b0 b1 g k0 k1")
assert S.cancel(g/b0-(-g)/b1-g*(b0+b1)/(b0*b1))==0
# Difference of two normalized true primitive errors at the same clock,
# using only their literal weighted entries, separates the G coefficient.
j,q,th,h=S.symbols("j q theta h")
assert S.expand((j-k0*q-th*h)-(j-k1*q-th*h)-(k1-k0)*q)==0
print("Exact early repeat primitives, paired head difference, companion subtraction", flush=True)

# Canonical reverse row words after dropping T and the last two rows.
# Labels are assigned by birth order, not by numerical comparison.
def words(w=(), counts=()):
    if len(w)==10:
        assert counts==(2,)*5
        yield w
        return
    for k,n in enumerate(counts):
        if n==1:
            yield from words(w+(k,),counts[:k]+(2,)+counts[k+1:])
    if len(counts)<5:
        n=len(counts)
        yield from words(w+(n,),counts+(1,))

c=Counter()
for w in words():
    assert tuple(w.index(i) for i in range(5))==tuple(sorted(w.index(i) for i in range(5)))
    if w.index(2)>2:
        c["pre-third return"]+=1
        continue
    n=w.index(3)
    assert w[:3]==(0,1,2) and 3<=n<=6
    if n>=5:
        c["at least two pre-fourth returns"]+=1
        continue
    if n==4:
        a=w[3]; nx=w[5]
        assert a in range(3) and nx!=a
        assert nx in (*range(4),4)
        c["one pre-fourth return, next "+("fifth" if nx==4 else "marked return")]+=1
        continue
    assert w[:4]==(0,1,2,3)
    x=w[4]; nx=w[5]
    if x==3:
        assert nx in (0,1,2,4)
        c["immediate fourth return, next "+("fifth" if nx==4 else "old return")]+=1
    elif x<3:
        assert nx!=x and nx in range(5)
        c["immediate old return, next "+("fifth" if nx==4 else "other return")]+=1
    else:
        assert x==4
        assert nx in range(5)
        c["consecutive fifth, next "+("old" if nx<3 else "fourth" if nx==3 else "fifth")]+=1
assert sum(c.values())==945
assert all(n>0 for n in c.values()) and len(c)==11
for case,n in sorted(c.items()):
    print(case, n)
print("Exact no-slack physical chronology census: 945 words, 11 nonempty leaves", flush=True)

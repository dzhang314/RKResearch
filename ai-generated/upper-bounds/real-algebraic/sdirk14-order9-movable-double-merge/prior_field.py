from sympy import Poly,symbols
from itertools import combinations
from functools import reduce,lru_cache
z=symbols('Z')
x=symbols('x')

def seed(p):
    return Poly(x**3-9*x*x+18*x-6,x,modulus=p)

def first_port(s,p):
    return Poly(x**4-(8*s*pow(3,-1,p)+8)*x**3+(2*s*s+16*s+12)*x*x
                -(8*s*s+16*s)*x+4*s*s,x,modulus=p)

def shifted_second(s,v,p):
    r=2*(3*s-v)%p
    assert r
    q=v*(2*s-v)*pow(r,-1,p)%p
    k=Poly((x-s)*(x-v)*(x-q),x,modulus=p)
    j=Poly(0,x,modulus=p)
    for (i,),a in k.terms():
        j+=Poly(int(a)*pow(i+1,-1,p)*x**(i+1),x,modulus=p)
    F=(j-k).exquo(Poly(x-v,x,modulus=p))
    assert F.degree()==3
    return F.monic()

def simple(F,a,p):
    assert int(F.eval(a))%p==0 and int(F.diff().eval(a))%p!=0

def irreducible(F,p,prime_divisor):
    # In the two cases n=3,4, n has exactly one distinct prime divisor.
    n=F.degree()
    X=Poly(x,x,modulus=p)
    def powX(m):
        W=Poly(1,x,modulus=p);B=X
        while m:
            if m&1:W=(W*B).rem(F)
            B=(B*B).rem(F)
            m>>=1
        return W
    assert powX(p**n)==X
    assert F.gcd(powX(p**(n//prime_divisor))-X).degree()==0

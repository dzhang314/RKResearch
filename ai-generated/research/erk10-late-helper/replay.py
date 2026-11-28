#!/usr/bin/env python3
"""Standard-library exact replay of the late-helper projective obstruction."""
from fractions import Fraction as Q
from functools import reduce
Z, O = Q(0), Q(1)

def clean(a):
    a = list(a)
    while a and not a[-1]:
        a.pop()
    return a

def scale(c, u):
    return clean([c*x for x in u])

def add(*terms):
    z = [Z]*max(map(len, terms), default=0)
    for a in terms:
        for i, b in enumerate(a):
            z[i] += b
    return clean(z)

def mul(a, b):
    if not(a and b):
        return []
    z = [Z]*(len(a)+len(b)-1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            z[i+j] += u*v
    return clean(z)

def pw(a,k):
    return reduce(mul, [a]*k, [O])

def hull(z):
    return reduce(mul, [[-x,O] for x in z], [O])

def sh(a, k=1):
    return [Z]*k+[Q(q) for q in a]

def quo(a, b):
    a = clean(a)
    c = [Z]*max(0, (len(a)-len(b)+1))
    while len(a) >= len(b):
        k = len(a)-len(b)
        c[k] = a[-1]/b[-1]
        a = add(a,scale(-c[k],sh(b,k)))
    assert not a
    return clean(c)

def mu(a,j=0):
    return sum((c/(i+j+1) for i,c in enumerate(a)), Z)

def ev(a,x):
    return reduce(lambda z,u:z*x+u, reversed(a), Z)

def pad(a, n):
    assert len(a)<=n
    return a+[Z]*(n-len(a))

X = [Z,O]
Y = [O,-O]
N = [Q(40),Q(-45),Q(12)]
D = scale(Q(15),pw([Q(-2),O],2))
P = [Q(20),Q(-15),Q(3)]
E = add(sh(N),scale(Q(-2),D))
W = add(scale(Q(3),sh(pw(N,2),2)),scale(Q(-15),sh(mul(N,D))),scale(Q(20),pw(D,2)))
J = quo(W,P)
R = []
for j in range(4):
    first = scale(Q(-8),sh(mul(pw(D,3-j),pw(N,j+1)),2))
    second = scale(Q(-(2**j)),sh(mul(mul([Q(2),-O],pw(N,3)),J),3-j))
    R.append(quo(add(first,second),mul(N,E)))
    assert len(R[-1])<=10

def functional(q, xi):
    return add(*(scale(z*xi**(j+2),R[j]) for j,z in enumerate(q)))

def quadratic(d,e,xi):
    # Nodal moments at the two anchors, the three fixed late sites and c.
    M = [mu(hull((Z,O,d,e,xi)),j) for j in range(5)]
    m0,m1,m2,m3 = ([M[k+1],-M[k]] for k in range(4))
    delta = add(mul(m0,m2),scale(-O,pw(m1,2)))
    ns = add(mul(m0,m3),scale(-O,mul(m1,m2)))
    np = add(mul(m1,m3),scale(-O,pw(m2,2)))
    Q0 = hull((d,e))
    f4 = mul(hull((Z,xi)),Q0)
    f5 = sh(f4)
    l4,l5 = functional(Q0,xi),functional(sh(Q0),xi)
    def k(f):
        a,b,c = (mu(mul(f,pw(Y,i))) for i in (2,3,4))
        # (constant, coefficient of the sum, coefficient of the product)
        return (2*b/3-a/2-c/4,a/2-b/3,-a/2)
    pressure = [add(scale(u,l5),scale(-v,l4)) for u,v in zip(k(f4),k(f5))]
    return tuple(
        add(*(scale(term[i],p) for term,p in zip((pad(delta,3),pad(ns,3),pad(np,3)),pressure)))
        for i in range(3)
    )

def red(q,p):
    return q.numerator*pow(q.denominator,-1,p)%p

def homev(a,n,x,y,p):
    return sum(z*pow(x,i,p)*pow(y,n-i,p) for i,z in enumerate(a))%p

def main():
    d,e,xi = Q(-1,8),Q(8,5),Q(1,4)
    C,B,A = quadratic(d,e,xi)
    disc = add(pw(B,2),scale(Q(-4),mul(A,C)))
    assert len(disc)==19
    mod=[red(x,29)for x in disc]
    squares={i*i%29 for i in range(29)}
    images=[homev(mod,18,i,1,29)for i in range(29)]+[homev(mod,18,1,0,29)]
    assert all(v not in squares for v in images)
    a,b,c = ([red(v,29) for v in pad(p,10)] for p in (A,B,C))
    assert a==[4,7,20,1,24,10,20,12,20,20]
    assert b == [23*v%29 for v in a] and c == [21*v%29 for v in a]
    end=[homev(a,9,i,1,29)for i in range(29)]+[homev(a,9,1,0,29)]
    donor=[homev([21,23,1],2,i,1,29)for i in range(29)]+[1]
    assert all(end) and all(donor)
    print('both homogeneous factors are nonzero on the 30 projective points')
    for j,c in enumerate((C,B,A)):
        print(f'c^{j} coefficient mod 29, ascending: {[red(x,29)for x in c]}')
    print('homogeneous degree-18 discriminant modulo 29, ascending:',mod)
    print('values at affine 0 through 28, then infinity:',images)
    print('all 30 are nonsquares; late clock residues:',tuple(red(x,29) for x in (d,e,xi)))
    # Independently confirm all formulas against the original rational linear functional.
    for t in map(Q,('1/2','2/3','3/2','5/2','3','4','5')):
        v=t*ev(N,t)/ev(D,t)
        alpha,beta=ev(N,t)/ev(D,t),2/t
        lam=v**3*(3*v*v-15*v+20)/16
        den=8*t*t*ev(D,t)**5/(ev(P,t)*ev(N,t)*ev(E,t))
        for q in (hull((d,e)),sh(hull((d,e)))):
            f=mul(hull((Z,xi)),q)
            l=ev(f,alpha*xi)-lam*ev(f,beta*xi)
            assert ev(functional(q,xi),t)==den*l

if __name__=='__main__':
    main()

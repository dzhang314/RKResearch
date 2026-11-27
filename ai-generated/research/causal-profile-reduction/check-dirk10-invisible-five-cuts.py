#!/usr/bin/env python3
"""Clock-only exact certificates for the five-distinct invisible DIRK10 face.
Prime 227 pays the forward first-interior and origin exclusions. Prime 59
pays the completely early ghost/fixed-factor reverse exclusion.
"""
from itertools import permutations
from math import prod

J = [1,-14,56,-84,42]  # 42 J_4, low coefficient first

def div(p,a,b):
    b %= p
    assert b
    return a*pow(b,-1,p)%p

def integ(p, a, coeffs, shift=0):
    return sum(div(p,c*a**(j+shift+1),j+shift+1) for j,c in enumerate(coeffs))%p

def determinant(p, rows):
    if not rows:
        return 1
    return sum((-1)**j*c*determinant(p,[a[:j]+a[j+1:] for a in rows[1:]])
               for j,c in enumerate(rows[0]))%p

def solve(p,nodes,rhs):
    d = len(nodes)
    A = [[x**k%p for x in nodes] for k in range(1,d+1)]
    den = determinant(p,A)
    assert den
    return [div(p,determinant(p,[row[:j]+[rhs[i]]+row[j+1:] for i,row in enumerate(A)]),den)
            for j in range(d)]

def times_root(p,c,r):
    z = [0]*(len(c)+1)
    for j,v in enumerate(c):
        z[j]=(z[j]-r*v)%p
        z[j+1]=(z[j+1]+v)%p
    return z

def roots(p):
    return [x for x in range(p) if not sum(c*x**j for j,c in enumerate(J))%p]

def anchored(p,clock):
    a,b=clock
    n=(1,2,3)
    i=lambda x,k:div(p,x**(k+1),k+1)
    return determinant(p,[
        [i(a,j) for j in n],
        [i(a,j+1) for j in n],
        [(i(b,j+1)-a*i(b,j))%p for j in n]
    ])

def clean_first(p,clock):
    a,b=clock
    T=lambda x:integ(p,x,J,1)
    i=lambda x,k:div(p,x**(k+1),k+1)
    return determinant(p,[
        [a**j%p for j in range(4)],
        [i(a,j+1) for j in range(4)],
        [i(b,j+1) for j in range(4)],
        [(T(b)*i(a,j+2)-T(a)*i(b,j+2))%p for j in range(4)],
    ])

for p,expected in ((227,[24,51,177,204]),(59,[14,23,37,46])):
    A=roots(p)
    assert A==expected
    assert all(integ(p,a,J,1) for a in A + [1])
    assert all(anchored(p,(a,b)) for a,b in permutations(A+[1],2))
    if p==227:
        assert all(clean_first(p,(a,b)) for a,b in permutations(A+[1],2))
    else:
        for a in A:
            U=[1]
            for h in A:
                if h!=a: U=times_root(p,U,h)
            assert all(integ(p,z,U,1) for z in A if z!=a)

p=59
def value(t,k):
    return div(p,t**(k+1),k+1)

def affine(u,v,c,d,x):
    return (c+div(p,(d-c)*(x-u),v-u))%p

def fixed_reverse(u,v,w,z):
    a,b,c,d = solve(p,[u,v,w,z],[value(z,k) for k in (1,2,3,4)])
    assert a and b and c  # three nonzero weighted taps from the fixed row
    hu = div(p,u**3,6)
    hv = div(p,-a*hu*(w-u),b*(w-v))
    hw = div(p,a*hu*(v-u),c*(w-v))
    assert hu and hv and hw
    tv,dv=solve(p,[u,v],[value(v,1),value(v,2)+hv])
    gamma_u = div(p,3*u,2)
    gamma_v = div(p,tv*u**3+dv*v**3-value(v,3),hv)
    L_u=div(p,u,2)
    L_v=div(p,tv*hu+dv*hv,hv)
    a,b,c=solve(p,[u,v,w],[value(w,1),value(w,2)+hw,
       value(w,3)+affine(u,v,gamma_u,gamma_v,w)*hw])
    return (a*hu+b*hv+c*hw-affine(u,v,L_u,L_v,w)*hw)%p

assert all(fixed_reverse(*q) for q in permutations(roots(p)))
print("227: 20 anchored and 20 first-interior determinant checks")
print("59: 20 anchored, 12 factor-primitive checks, and 24 reverse consistency failures")

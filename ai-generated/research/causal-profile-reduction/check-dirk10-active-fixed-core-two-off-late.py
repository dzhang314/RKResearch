#!/usr/bin/env python3
"""Independent exact one-late gates; no tableau coefficients used."""
from itertools import permutations

for p in (419,587):
    I=tuple(t for t in range(p) if (42*t**4-84*t**3+56*t*t-14*t+1)%p==0)
    assert len(I)==4
    def d(a,b):
        assert b%p
        return a*pow(b%p,-1,p)%p
    for U,W,R,X in permutations(I):
        z=d(10*R*U*U-25*R*U*W+10*R*W*W+U*U*W+U*W*W,6*(U-W)**2)
        assert z not in (0,1,*I)
    for xi,x in permutations(I,2):
        a=d(x*(5*xi-3*x),5*(2*xi-x))
        assert a not in (0,1,*I)
        h=d(xi**2*a**3,36*(a-xi)); gamma=d(xi**3,6)
        alpha=d(3*(a-xi)*(a-2*xi),xi**2)
        Sxi=d(x**3*(2*a-x),12*xi*(xi-a)*(xi-x))
        Sa=d(x**3*(2*xi-x),12*a*(a-xi)*(a-x))
        delta=(alpha*Sa*h-(a-d(xi,2))*gamma*Sxi)%p
        assert delta and delta==d(x**4*(10*xi*xi-12*xi*x+3*x*x)**2,
                                   720*(2*x-5*xi)*(x-2*xi)*(x-xi))
    print(f"mod {p}: 24 location guards and 12 true forward one-late obstructions pass")

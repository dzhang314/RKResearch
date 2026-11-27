#!/usr/bin/env python3
"""Independent replay of the irreducibility places and 31-adic ingress."""
from lift_assembly import moment
from flint import fmpz_mod_ctx,fmpz_mod_poly_ctx

def sc(p,s,t):
    F=fmpz_mod_ctx(p); Q=fmpz_mod_poly_ctx(F)
    a,z,P,D,B0,B1=moment(F,Q,Q.gen(),F(s),F(t))
    return tuple(map(int,(z,D,B0,B1)))

ps=lambda s:s**3-9*s*s+18*s-6
ds=lambda s:3*s*s-18*s+18
pt=lambda s,t:t*t-(s+3)*t+s
dt=lambda s,t:2*t-s-3
def nonsquare(t,p):
    return not any(x*x%p==t%p for x in range(p))

assert ps(7)%11==0 and ds(7)%11==6
assert ((7+3)**2-4*7)%11==6 and nonsquare(6,11)
assert ps(9)%13==0 and ds(9)%13==8
assert pt(9,7)%13==0 and dt(9,7)%13==2
assert sc(13,9,7)==(1,7,8,12)
assert (12**2-4*8)%13==8 and nonsquare(8,13)
assert (ps(11)%31,ds(11)%31,pt(11,17)%31,dt(11,17)%31)==(0,28,0,20)
assert sc(31,11,17)==(17,4,1,19)
assert (4**2+19*4+1)%31==0 and (2*4+19)%31==27
print('11 and 13 irreducibility places and simple 31-adic ingress verified')

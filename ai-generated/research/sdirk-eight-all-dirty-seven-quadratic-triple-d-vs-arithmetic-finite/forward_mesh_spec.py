"""Literal two overlap products for D,D,D versus exactly one additional D."""
import sympy as S
from itertools import product
from sympy.polys.fields import field
from sympy.polys.rings import ring
Q,h=field('h',S.QQ)
x=S.Symbol('h')
qu=lambda r:Q(S.Rational(r))
def k(u):return 1+2*u-u*u
def H(u):return -2+u+4*u*u-u**3
def num(u):return (1+4*u-4*u*u)*H(u)+4*u*u*(3*u-2)
def g(u,mode):
    return num(u)/(2*H(u)) if mode=='A' else k(u)/2
def phaseguards(u,mode):
    return [u,k(u),H(u),num(u),3*u-2] if mode=='A' else [u,k(u),u-1,u-2]
def l4(t,m):return t**4-qu(S.Rational(6,7))*m*m*t*t+qu(S.Rational(3,35))*m**4
def sqroot(a,b,m):return 35*a*a*b*b-21*m*m*(a*a+b*b)+15*m**4
def f_specs():
    pp=Q.one
    yield 'AM','A',h+1,[-h,Q.zero,h],h,pp # no additional Q condition
    yield 'AN','A',h+1,[-h,h,3*h],2*h,sqroot(h,3*h,h+1)
    d=2-3*h
    for mode,D,u in [('S1',[-h,h,d],2*h),('S2',[-h,d,h],2-2*h)]:
        yield mode,'S',h+1,D,u,d*sqroot(h,d,h+1)
    yield 'C_A','A',pp,[Q.zero,h,2*h],h,sqroot(h,2*h,pp)
    yield 'C_S','S',pp,[Q.zero,h,2-h],h,sqroot(h,2-h,pp)

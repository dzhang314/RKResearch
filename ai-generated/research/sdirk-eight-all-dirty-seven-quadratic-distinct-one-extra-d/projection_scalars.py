"""Both distinct doubled endpoints, extra D labels mutually reusing them."""
import sympy as S
from itertools import combinations_with_replacement
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from time import monotonic

F,h,d=field('h,d',S.QQ)
X=S.Symbol('h')
C=MC.get(('h','d'),'lex')
hh,dd=C.gens()
m=h+1
def L(t):return t**4-F(6)*m*m*t*t/7+F(3)*m**4/35
def k(u):return 1+2*u-u*u
def D(u):return -2+u+4*u*u-u**3
def N(u):return (1+4*u-4*u*u)*D(u)+4*u*u*(3*u-2)
kap=k(2*h)/2
delta=35*h*h-21*m*m
S0=(21*m*m*h*h-15*m**4)/delta
Th=35*hh*hh*dd*dd-21*(hh+1)**2*(hh*hh+dd*dd)+15*(hh+1)**4
ThF=35*h*h*d*d-21*m*m*(h*h+d*d)+15*m**4
def integer(p):
    if not p:return C.constant(0)
    den=lcm(*(int(S.Rational(c).q) for c in p.values()))
    return C.from_dict({tuple(map(int,ij)):int(c*den) for ij,c in p.items()})
def strip(f,gs):
    if not f:return f
    for g in gs:
        while (p:=f.gcd(g)).total_degree()>0:
             f,r=divmod(f,p);assert not r
    return f

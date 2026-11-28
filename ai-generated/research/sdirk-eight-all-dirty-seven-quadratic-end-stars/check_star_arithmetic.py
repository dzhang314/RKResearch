"""Exact reverse arithmetic gates when a doubled endpoint opens with two singleton stars."""
import sympy as S
from sympy.polys.rings import ring
x=S.Symbol('x')
def hub(v):return -2+v+4*v*v-v**3
def kap(v):return 1+2*v-v*v
def qnum(v):return (1+4*v-4*v*v)*hub(v)+4*v*v*(3*v-2)
def try_mesh(name,K,ell,z):
    R,v=ring('v',K)
    m=ell/2
    LL=(v+(2-m))**4-(v+(2-m))**2*(K.convert(S.Rational(6,7))*m*m)+K.convert(S.Rational(3,35))*m**4
    W=LL%(v*v-z)
    l0,l1=W.get((0,),K.zero),W.get((1,),K.zero)
    assert l0 or l1
    a=-v+(ell-3);b=-2*v+(ell-3)
    mask=-(a+b)*l0-(a*b+z)*l1
    read=qnum(v)*(a*a-z)-kap(v)*hub(v)*(b*b-z)
    gc=mask.gcd(read).monic()
    print(name,'mask deg',mask.degree(),'read deg',read.degree(),'gcd deg',gc.degree(),flush=True)
    if gc.degree()>0:
      print('gcd',gc.as_expr(),flush=True)
    return gc

def meshes():
    yield 'even',S.QQ,S.QQ(4),S.QQ(156,49)
    F=S.Poly(560*x**4-560*x**3-217*x*x+336*x-69,x)
    assert F.is_irreducible
    K=S.QQ.algebraic_field((F,x));e=K.unit
    d=4*e-2;ell=2*K.one/(1-e)
    assert e and d and d*d!=e*e
    yield 'split distinct endpoints',K,ell,(ell*d/4)**2
    F=S.Poly(35*x*x+42*x-69,x);assert F.is_irreducible
    K=S.QQ.algebraic_field((F,x));t=K.unit
    yield 'split same endpoint',K,K(2),1-t

for args in meshes():
    gc=try_mesh(*args)
    assert gc.degree()==0 or (args[0]=='even' and gc.as_expr()==S.Symbol('v')-S.Rational(2,3))

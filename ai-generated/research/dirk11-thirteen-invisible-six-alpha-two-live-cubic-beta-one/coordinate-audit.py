"""Independent exact coordinate checks for the new local gates."""
from pathlib import Path
from runpy import run_path
from random import Random
import sympy as S
D=run_path(str(Path(__file__).with_name('ordinary.py')))
Y,V,R,DR=(D[k]for k in ('Y','V','R','D'))
X,b=S.symbols('X b')
# Do not define either primitive via the other. Their variables, endpoints
# and orientation are checked in all four symbolic basis coefficients.
m=S.symbols('m0:4')
U=sum(m[i]*Y**i for i in range(4))
left=S.integrate(X*U.subs(Y,1-X),X)
right=S.integrate((1-Y)*U,Y)
assert S.expand(left.subs(X,b)-left.subs(X,0)
                -right.subs(Y,1)+right.subs(Y,1-b))==0
assert S.expand(D['L0']/60-(S.integrate(Y*R,Y)/Y))==0
assert S.expand(D['L1']/60-(S.integrate(Y**2*R,Y)/Y))==0

rng=Random(514725)
for _ in range(8):
    ff=U.subs(dict(zip(m,(S.Rational(rng.randint(-11,11),rng.randint(1,13))for _ in m))))
    Bq=S.Rational(rng.randint(-9,8),11)
    ji=S.integrate(X*ff.subs(Y,1-X),(X,0,1-Bq))
    ai=S.integrate((1-Y)*ff,(Y,Bq,1))
    assert ji==ai

# A second check compares the coefficient matrices with literal
# evaluations on three old clocks and V, independent of the symbolic
# quotient code used for the exact ordinary projection.
for _ in range(6):
    pts=[S.Rational(j,23)for j in rng.sample(range(-10,20),4)]
    p0,p1,p2,vs=pts
    rr=(Y-p0)*(Y-p1)*(Y-p2)
    rc=S.Poly(rr,Y)
    sub={V:vs,**{D[f'c{i}']:rc.nth(i)for i in range(3)}}
    xx=S.Rational(rng.randint(-15,15),17)
    j=D['J4'](Y)
    l=D['L0'].subs(sub);m1=D['L1'].subs(sub)
    for pols in ((j,l,Y*l,m1),(j,Y*j,(Y-xx)*l,Y*(Y-xx)*l)):
        ev=S.Matrix([[p.subs(Y,v)for p in pols]for v in pts]).det()
        mod=S.Poly((Y-vs)*rr,Y)
        cs=S.Matrix([[S.rem(S.Poly(p,Y),mod).nth(q)for p in pols]for q in range(4)]).det()
        vand=S.prod(pts[j]-pts[i]for i in range(4)for j in range(i+1,4))
        assert ev==vand*cs
print('Independent QQ coordinate audit: symbolic primitives, 8 rational reflections, and both 4-clean determinants checked.')

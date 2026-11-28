"""Independent exact Y-oriented primitive and matched old determinant audit."""
from pathlib import Path
from runpy import run_path
from random import Random
import sympy as S
a=run_path(str(Path(__file__).with_name('ordinary.py')))
Y,V,R=a['Y'],a['V'],a['R']
L0,L1=a['L0'],a['L1']
assert S.expand(L0/60-S.integrate(Y*R,Y)/Y)==0
assert S.expand(L1/60-S.integrate(Y**2*R,Y)/Y)==0
assert S.expand((Y-V)*a['ND']-a['N'])==0
rng=Random(71852)
for _ in range(8):
    ix=[S.Rational(i,37)for i in rng.sample(range(-15,20),4)]
    v=ix[-1];xs=ix[:3]
    r=S.Poly(S.prod(Y-x for x in xs),Y)
    mp={V:v,**{a[f'c{k}']:r.nth(k)for k in range(3)}}
    J=a['J4'](Y); n=a['N'].subs(mp); nd=a['ND'].subs(mp)
    l=[n,Y*n,(Y-v)*J]; ll=[nd,Y*nd,J]
    orig=S.Matrix([[f.subs(Y,x)for f in l]for x in xs]).det()
    coef=S.Matrix([[S.rem(S.Poly(f,Y),r).nth(k)for f in ll]for k in range(3)]).det()
    vd=S.prod(xs[j]-xs[i]for j in range(3)for i in range(j))
    assert orig==vd*S.prod(x-v for x in xs)*coef
print('Independent rational audit: reverse primitives and eight literal three-clock samples agree.')

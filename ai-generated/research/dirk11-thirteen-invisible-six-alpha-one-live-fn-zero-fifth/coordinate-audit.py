"""Independent QQ check of the fixed-degree linear pin and reflected primitive."""
import sympy as S
from random import Random
t,c0,c1,c2,b0,b1=S.symbols('t c0 c1 c2 b0 b1')
res=S.resultant(c0+c1*t+c2*t*t,b0+b1*t,t)
assert S.expand(res-(c0*b1*b1-c1*b0*b1+c2*b0*b0))==0
x,y,B,L=S.symbols('x y B L')
a=S.symbols('a0:4')
M=sum(a[i]*y**i for i in range(4))
rev_primitive=S.integrate((L-y)*M,y)
fwd=S.integrate(x*M.subs(y,L-x),x)
assert S.expand(fwd.subs(x,L-B)-fwd.subs(x,0)-
                rev_primitive.subs(y,L)+rev_primitive.subs(y,B))==0
rng=Random(5927241)
for _ in range(8):
    op=dict(zip(a,(S.Rational(rng.randint(-9,10),rng.randint(1,17))for _ in a)))
    op.update({L:S.Rational(rng.randrange(1,5),7),B:S.Rational(rng.randrange(-5,7),11)})
    assert S.expand((fwd.subs(x,L-B)-fwd.subs(x,0)).subs(op)-
                  (rev_primitive.subs(y,L)-rev_primitive.subs(y,B)).subs(op))==0
print('Exact QQ quadratic-linear resultant and symbolic/8 rational forward-reverse primitive checks passed.')

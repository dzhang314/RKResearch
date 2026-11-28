"""Recreate the genuine old first-ghost affine remainder before specializing F1."""
import sympy as S
c0,c1,c2,r,s,Y,a=S.symbols('c0 c1 c2 r s Y a')
D=c0*r*r-(2*s*s+c1*s)*r+3*c2*s*s-3*c0*s
R=Y**3+c2*Y**2+c1*Y+c0;m=Y**2+r*Y+s
def vec(f):
 p=S.Poly(S.rem(f,R,Y),Y);return S.Matrix([p.nth(i)for i in range(3)])
A=S.Matrix.hstack(*(vec(m*Y**i)for i in range(3)))
n=A.det().expand()
w=A.adjugate()*vec(S.cancel(S.integrate(Y*R,Y)/Y))
p=r*c0;q=3*s*c2-4*r*s-3*c0
H=sum(w[i]*p**i*q**(2-i)for i in range(3))
Z=S.Poly(S.rem(H,D,r),r)
eq=lambda a,b:S.cancel(a-b)==0
sub={c0:a*s,c1:S.Rational(6,5)*s+S.Rational(15,16)*a*(c2-a)}
rd=S.Rational(15,16)*(c2-a)
rl=16*s/(5*a)
F1=96*s**3-80*c1*s*s+75*c0*c2*s-75*c0*c0
assert eq(F1.subs(sub),0)
assert eq(D.subs(sub),s*(r-rd)*(a*r-16*s/5))
assert eq(S.Rational(1,4)-rd/(12*(c2-rd-a)),-1)
D1=192*s-25*a*a-25*a*c2
D2=5*a*a-5*a*c2+16*s
A1=-3*s**4*D1*D2**2/(1250*a)
assert Z.degree()==1
assert eq(Z.nth(1).subs(sub),A1) and eq(Z.nth(0).subs(sub),-rd*A1)
assert eq(n.subs(r,rl).subs(sub),-s*(-225*a*a+512*s)*D2**2/(6400*a*a))
sub2={c2:192*s/(25*a)-a}
assert eq(c1.subs(sub).subs(sub2),42*s/5-15*a*a/8)
assert eq((25*a**3+25*c2*a**2-192*c0).subs(sub).subs(sub2),0)
assert eq((15*c2*a**2-8*c1*a-48*c0).subs(sub).subs(sub2),0)
# Heights are homogeneous when using the cleared gauge 5 a² m.
assert eq((5*a**2*m.subs(r,rl)).subs(s,c0/a),5*a**2*Y*Y+16*c0*Y+5*a*c0)
print('Exact alternate F1 old affinity, affine remainder, old determinant, and eliminated coefficients checked.')

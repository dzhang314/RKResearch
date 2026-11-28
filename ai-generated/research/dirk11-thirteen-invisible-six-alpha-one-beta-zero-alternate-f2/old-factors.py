"""Recreate the old determinant and affine remainder before specializing F2."""
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
eq=lambda x,y:S.cancel(x-y)==0
sub={c0:a*s,c1:s+a*(c2-a)}
rd=c2-a
rl=3*s/a
C=a*a-a*c2+3*s
D1=7*s-a*a-a*c2
D2=5*a*a-5*a*c2+16*s
A1=-3*s**4*D1*C*D2/(10*a)
assert Z.degree()==1
assert eq(R.subs(sub),(Y+a)*(Y**2+rd*Y+s))
assert eq(D.subs(sub),s*(r-rd)*(a*r-3*s))
assert eq(Z.nth(1).subs(sub),A1) and eq(Z.nth(0).subs(sub),(a-c2)*A1)
assert eq(n.subs(r,rl).subs(sub),-s*(-a*a+2*s)*C*C/(a*a))
assert eq(q.subs(r,rl).subs(sub),-3*s*(a*a-a*c2+4*s)/a)
# The last factor returns the old slope -1, through the actual IP coefficient.
ee=(c2-rl-a).subs(c2,a+16*s/(5*a))
assert eq(ee,s/(5*a))
assert eq(S.Rational(1,4)-rl/(12*ee),-1)
# Surviving gauge: X is the actual singled old ordinary clock -a.
X=S.symbols('X')
sub2={c2:7*s/a-a}
assert eq((c2-a).subs(sub2).subs(a,-X),2*X-7*s/X)
assert eq((p/q).subs(r,rl).subs(sub).subs(sub2).subs(a,-X),X*s/(2*X**2-3*s))
print('Exact alternate F2 old affinity, affine remainder, old determinant, and survivor coordinates checked.')

"""Reproduce the literal old remainder, derivative ingress and H3 contact."""
import sympy as S
Y,c0,c1,c2,r,s=S.symbols("Y c0 c1 c2 r s")
R=Y**3+c2*Y**2+c1*Y+c0;m=Y**2+r*Y+s
P=Y*m;P0=Y*R
def v(f):
    a=S.Poly(S.rem(f,R,Y),Y)
    return S.Matrix([a.nth(i)for i in range(3)])
M=S.Matrix.hstack(*(v(m*Y**i)for i in range(3)))
w=M.adjugate()*v(S.cancel(S.integrate(P0,Y)/Y))
D1=-s*(2*s+c1);D0=3*s*(c2*s-c0)
D=c0*r*r+D1*r+D0
q=3*s*c2-4*r*s-3*c0
p=r*c0
H=sum(w[i]*p**i*q**(2-i)for i in range(3))
Z=S.Poly(S.rem(H,D,r),r)
A0,A1=Z.nth(0),Z.nth(1);assert Z.degree()==1
factual=c0*A0**2-D1*A0*A1+D0*A1**2
f1=96*s**3-80*c1*s**2+75*c0*c2*s-75*c0**2
f2=s**3-c1*s*s+c0*c2*s-c0*c0
fn=12*c2*s**3-(36*c0+4*c1*c2)*s*s+(-12*c0*c1+12*c0*c2*c2-c1*c1*c2)*s-c0*c1*c1
eq=lambda a,b:S.cancel(a-b)==0
assert eq(S.resultant(D,Z.as_expr(),r),factual)
up=S.Rational(3,100)*(c2*s-c0)**2*f1*f2**2
assert eq(factual,up*fn)
# A0,A1 each kill the literal derivative, without assuming they vanish
# as polynomials in s. Abstract the evaluations and differentiate first.
aa,bb,cc,dd=[S.Function(x)(s) for x in ("aa","bb","cc","dd")]
Rm=c0*aa*aa-cc*aa*bb+dd*bb*bb
assert eq(S.diff(Rm,s).subs({aa:0,bb:0}),0)
assert eq(fn.subs(c2,0),-c0*(c1+6*s)**2)
# Optional independent check of the repeated and triple root on H3.
sub=-c1*c1*c2/(9*(2*c1-c2*c2))
sg=fn.subs(c0,sub)
assert eq(sg,c2*(6*s-c1)**2*(c1*c1+6*c1*s-3*c2*c2*s)/(9*(2*c1-c2*c2)))
assert eq((c1*c1+6*c1*s-3*c2*c2*s).subs(s,c1/6),c1*(4*c1-c2*c2)/2)
at={c1:c2*c2/4,c0:c2**3/72,s:c2*c2/24}
assert eq(D.subs(at),c2**3*(r-c2/2)**2/72)
assert eq(q.subs(at).subs(r,c2/2),0)
print("Actual first-ghost affine remainder and profile resultant; repeated-Fn derivative and H3 triple-contact checks passed.")

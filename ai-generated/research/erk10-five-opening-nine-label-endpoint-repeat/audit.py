"""Independent later-endpoint minors and causal transfer checks."""
import sympy as S
b,c,z,k,Y,w,u=S.symbols("b c z k Y w u")
q=S.Rational
same=lambda f,g:S.cancel(f-g)==0
D=3*b*k-2*c*k+c
Lb=-2*(1+2*k*(b-1))/b**2
Lc=-2*(2*b*c*k*k+2*b*c*k-2*b*k*k+b*k-2*c*k+c)/(c*c*D)
P=2*z/3+k*(4*b/3-2)*(z-1)
Q=k*(z-1)+b*k*(z-1)*(z-b)/D
R=z*z/2+k*(b*b-2)*(z-1)-b*k*(b*k-c*k-c+2)*(z-1)*(z-b)/D
A=S.Matrix([[1,1,-k],[-2,b*Lb,1],[-2,b*b*Lb,P.subs(z,0)]])
assert same(A.det(),-4*k*(b-1)*(2*k-1)/3)
print("jump after two interiors:",S.factor(A.det()))
B=S.Matrix([[1,1,1,-k],[1,b,c,Q.subs(z,0)],[-2,b*b*Lb,c*c*Lc,P.subs(z,0)],
            [-2,b**3*Lb,c**3*Lc,R.subs(z,0)]])
assert same(B.det(method="domain-ge"),-4*b*b*c*k**3*(b-1)*(b-c)*(c-1)*(2*k-1)/D**2)
print("jump after three interiors:",S.factor(B.det(method="domain-ge")))
assert same((P+2*Q).subs(k,q(1,2)),2*z*z/3)
assert S.expand(w*Y**3/3+2*Y**2*u/3-(Y/3)*(Y*(w*Y+2*u)))==0
assert S.expand(w*Y**4/4+Y*Y*u/2-(Y/4)*(Y*(w*Y**2+2*u)))==0
assert S.expand(((Y*Y/2-(Y-1)*(Y-b))+(Y-1)*(Y-b))-Y*Y/2)==0
print("global causal transfers KF=YF/3 and KF=YF/4 verified")

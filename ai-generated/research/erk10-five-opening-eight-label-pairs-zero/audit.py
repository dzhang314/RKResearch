"""Exact dormant coefficients and raw terminal adapter for both heads."""
import sympy as S
a,b,c,z,x,Y,w1,w2,W,u,H,g,L,S0,T = S.symbols("a b c z x Y w1 w2 W u H g L S0 T")
q=S.Rational
F=lambda r,s,z:-z*z/4+(r+s)*z/3-r*s/2
same=lambda x,y:S.cancel(x-y)==0

# Immediate active closing head, next row at dormant b.
be=-q(2,3)
ph=-a-(b-a)*(z-a)/(2*b-3*a)
ps=-a*(z-a)/(2*b-3*a)
Q,D=(2*b-a)/4,-a/2
m=ph-(a+b)*be;n=ps-Q*be-D
b0=b*(2*a-b)/(3*(3*a-2*b))
assert same(m.subs(z,b),b0) and same(n.subs(z,b),2*b0)
assert same(m.subs(b,2*a),2*a-z)
assert same(F(a,b,z).subs(b,2*a),-(z-2*a)**2/4)
print("immediate active close: dormant dual coefficients",S.factor(b0),S.factor(2*b0))

# Single intermediate b, active closure, then attempted repeat b.
be=(4*b-6*a)/(3*a)
pb=b*b/a-2*a
pa=(a+b)*be-b*(a-2*b)/(3*(3*b-2*a))
psa=b*(a-b)/(3*b-2*a)
ph=pb+(z-b)*(pa-pb)/(a-b)
ps=(z-b)*psa/(a-b)
Q,D=a*(2*a-b)/(4*b),-a*(3*b-2*a)/(2*b)
m=ph-(a+b)*be;n=ps-Q*be-D
assert same(m.subs(z,b),b*(2*a-b)/(3*a)) and same(n.subs(z,b),(a+b)/3)
assert S.expand((2*a-b)+(a+b)-3*a)==0
print("one intermediate singleton: repeat b cannot kill both coefficient factors")

# Two intermediate distinct labels a,b,c, next b or c.
hc=a*c*c*(2*c-3*b)/(4*b)
pc=c*c*F(a,b,c)/hc+(a+b)*be
ph=pb+(z-b)*(pc-pb)/(c-b)
ps=-b*(z-b)/(2*c-3*b)
Q=a*(2*c-b)/(4*b)
D=-c+a*(2*c-b)/(2*b)
eta=-a/(2*(a-b)*(a-c))
m=ph-(b+c)*be-1/eta;n=ps-Q*be-D
assert same(m.subs(z,b),b*(2*c-b)/(3*a)) and same(n.subs(z,b),(b+c)/3)
assert same(m.subs(z,c),b*c*(2*b-c)/(3*a*(3*b-2*c)))
assert same(n.subs(z,c),2*c*(2*b-c)/(3*(3*b-2*c)))
assert same(m.subs(c,2*b),-b*(z-2*b)/a)
assert same((m*a*z*z*(z-c)/(4*b)-z*z*F(b,c,z)).subs(c,2*b),0)
print("second head: exact (weighted) sixth-row closed-group transfer")

# Corrected donor vectors at a1/a2: no w2 or pooled score division.
u1=-w1*a*a/2
u2=+w1*a*a/2
M=a*a*(a-b)**2
G1=w1*g+2*g*u1/a**2
G2=w2*g+2*g*u2/a**2
Z1=-w1*M/4-(a-b)**2*u1/2
Z2=(a-b)*H-w2*M/4-(a-b)**2*u2/2
assert S.expand(G1)==0 and S.expand(Z1)==0
assert S.expand(G2-(w1+w2)*g)==0
assert S.expand(Z2-((a-b)*H-(w1+w2)*M/4))==0
print("deferred closing copy exactly carries raw pooled G,Z, whatever its score")

# Common exact old scalar rank-one square after adding the reference site.
E2=z*z*L+2*z*T-x*x
E3=z**3*L+3*z*z*T-x**3
E4=z**4*L+4*z**3*T-x**4
assert S.expand(z*z*E2-2*z*E3+E4+x*x*(x-z)**2)==0
print("aggregate-exact branch calibrated square:",S.factor(z*z*E2-2*z*E3+E4))

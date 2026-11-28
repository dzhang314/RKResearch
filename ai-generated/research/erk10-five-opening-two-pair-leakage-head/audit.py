#!/usr/bin/env python3
"""Three exact chronological determinant shapes and one symmetric mesh gate."""
import sympy as S
a,b,c,z,Y,U,V=S.symbols('a b c z Y U V')
kap=lambda z:-z*z/4+(a+b)*z/3-a*b/2
def checks(F,G,X,Y,want):
    assert S.cancel(X*G-Y*F-want)==0
    print('determinant:',S.factor(want))
# A,A,b,z.
F=(5*a*b-3*a*z-4*b*b+3*b*z)/(3*(3*a-2*b))
G=(a*b+3*a*z-2*b*b)/(3*(3*a-2*b))
checks(F,G,kap(z),-a*b/4+(2*b-a)*z/12,a*(a-z)*(b-z)**2/(4*(3*a-2*b)))
assert S.cancel(F.subs(z,b)-b*(2*a-b)/(3*(3*a-2*b)))==0
assert S.cancel(G.subs(z,b)-2*F.subs(z,b))==0
# A,b,A,z.
F=b*(4*a*a-5*a*b-3*a*z+3*b*z)/(3*a*(2*a-3*b))
G=(2*a*a-a*b-3*b*z)/(3*(2*a-3*b))
checks(F,G,kap(z),-a*a/4+a*(2*a-b)*z/(12*b),-b*(a-z)**2*(b-z)/(4*(2*a-3*b)))
assert S.cancel(F.subs(z,b)-b*(2*a-b)/(3*a))==0
assert S.cancel(G.subs(z,b)-(a+b)/3)==0
# A,b,c,z, with A still open at c.
F=-b*(-5*b*c+3*b*z+4*c*c-3*c*z)/(6*(a-b)*(a-c)*(3*b-2*c))
G=(b*c+3*b*z-2*c*c)/(3*(3*b-2*c))
checks(F,G,-a*(z*z/4-(b+c)*z/3+b*c/2)/(2*(a-b)*(a-c)),
       -a*c/4+a*(2*c-b)*z/(12*b),
       -a*b*(z-b)*(z-c)**2/(8*(a-b)*(a-c)*(3*b-2*c)))
assert S.cancel(F.subs(z,b)-b*(2*c-b)/(6*(a-b)*(a-c)))==0
assert S.cancel(G.subs(z,b)-(b+c)/3)==0
assert S.cancel(G.subs(z,c)-2*c*(2*b-c)/(3*(3*b-2*c)))==0
# The two coefficient rows were computed independently from the
# actual normalized h means in the three head shapes.
assert S.cancel(F.subs(z,c)-b*c*(2*b-c)/(6*(a-b)*(a-c)*(3*b-2*c)))==0
print('all dormant-repeat coefficient guards checked')
# Symmetric a=1/3,b=2/3,next ordinate c=1/2.
I=lambda f:sum(t/(i+1)for (i,),t in S.Poly(f,Y).terms()if i%2==0)
J=(Y*Y-1)*(Y*Y-S.Rational(1,9))*(Y*Y-U)*(Y*Y-V)
ma=I(S.cancel(Y*J/(Y+S.Rational(1,3))))
mc=I(J)
assert S.expand(3*mc-4*ma-16*(7*U*V-2*U-2*V+1)/315)==0
print('symmetric center pressure: 7*U*V-2*U-2*V+1=0')

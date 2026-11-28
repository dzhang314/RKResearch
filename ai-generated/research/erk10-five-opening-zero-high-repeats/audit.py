"""Symbolic checks of repeat/zero adaptations, not a search."""
import sympy as S
a,p,c,z,A,B,w,l,T,x,Y,e,f,g,d = S.symbols("a p c z A B w l T x Y e f g d")
q=2*p
E = lambda f: S.factor(f)==0
mat=S.Matrix([[a,p],[2*a*p,3*p*p]])
assert E(mat.det()-a*p*p)
print("pure ghost, extra endpoint after first normal: two-tap determinant =",S.factor(mat.det()))
assert E((z**2*l+2*z*T-x*x)*z*z
       -2*z*(z**3*l+3*z*z*T-x**3)+(z**4*l+4*z**3*T-x**4)+x*x*(x-z)**2)
print("tracked ghost-plus-pair two-target exit: x^2*(x-z)^2")
L=5*p*c-3*p*z-4*c*c+3*c*z
N=p*c+3*p*z-2*c*c
M=-3*z*z+4*(p+c)*z-6*p*c
J=(2*c-p)*z-3*p*c
assert E((L*J-N*M).subs(z,0)+9*p*p*c*c)
assert E((p*L/(3*a*(3*p-2*c))).subs(c,q)+p*(z-q)/a)
assert E(M.subs(c,q)/12+(z-q)**2/4)
print("endpoint-after-two determinant and dormant q=2p cubic specialization checked")
M=Y*Y*(Y-q)**2; G=Y*(Y-p)*(Y-q)*(Y-c)
prim=lambda f:S.integrate(f,(Y,0,z))
assert E(4*prim(G)-(z-c)*M.subs(Y,z)+prim(M))
# Both raw corrections vanish at a=1 with u=-w*a^2/2, H=0.
assert E(w*G.subs(Y,a)+2*G.subs(Y,a)*(-w*a*a/2)/(a*a))
assert E(-w*M.subs(Y,a)/4-(a-q)**2*(-w*a*a/2)/2)
assert S.cancel(1/((p-c)*(p-d))+1/((c-p)*(c-d))+1/((d-p)*(d-c)))==0
print("corrected high-zero donors, blind primitive identity and cofactor collapse checked")

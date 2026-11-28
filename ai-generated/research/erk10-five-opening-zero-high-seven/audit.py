"""Exact seven-visible census and polynomial receipts for new transfers."""
import sympy as S
a,b,p,q,c,z,t,u,v,s,A,B,T,w,H,L,Z,Y,x = S.symbols("a b p q c z t u v s A B T w H L Z Y x")
eq=lambda x:S.cancel(x)==0
cases=[(r,e,3-r-e) for r in range(1,4) for e in range(4-r)]
assert cases==[(1,0,2),(1,1,1),(1,2,0),(2,0,1),(2,1,0),(3,0,0)]
print("seven visible labels (zero rows, endpoint excess, interior excess):",cases)
assert eq((a*A+b*B)*3*b-(2*a*b*A+3*b*b*B)-a*b*A)
assert eq((2*a*b*A+3*b*b*B)-2*b*(a*A+b*B)-b*b*B)
F=lambda p,q,z:-z*z/4+(p+q)*z/3-p*q/2
for expr in [a*(z-a)*(z-b)**2/(4*(3*a-2*b)),
             b*(z-a)**2*(z-b)/(4*(2*a-3*b)),
             b*(z-b)*(z-c)**2/(4*(3*b-2*c))]:
    assert S.factor(expr.subs(z,0))!=0
print("early added endpoint: homogeneous two-tap solve and all three z=0 factors checked")
Bz=z*z*(2*z-3*a)/(6*b*(b-a))
assert eq(z*z*F(a,b,z)-b*(a-b)*(a-2*b)*Bz/2+z*z*(z-a)**2/4)
print("invisible double label: exceptional target residual = -z^2*(z-a)^2/4")
triple=2*t*t*(2*(a*A+t*T))-4*t*(3*(a*a*A+t*t*T))+(9*a**3*A+8*t**3*T)
assert eq(triple-a*(2*t-3*a)**2*A)
assert eq(2*t*t*w*x*x-4*t*w*x**3+2*w*x**4-2*w*x*x*(x-t)**2)
yt=3*a/2; St=w*yt**2/(2*a)
assert eq(a**3*St-w*yt**4/4+a*(a*a*St/2)/4)
print("tripled endpoint: independent k_t value and corrected terminal square checked")
M=Y**2*(Y-2*p)**2
G=Y*(Y-p)*(Y-2*p)*(Y-c)
Jl=lambda f:S.integrate(f,(Y,0,z))
assert eq(4*Jl(G)-(z-c)*M.subs(Y,z)+Jl(M))
assert eq(1/(p*(p-c))+1/(c*(c-p))+1/(p*c))
assert eq(1/((p-c)*(p-s))+1/((c-p)*(c-s))+1/((s-p)*(s-c)))
assert eq(S.diff(M,Y)/4-Y*(Y-p)*(Y-2*p))
print("ghost + added endpoint: blind primitive and both nodal cofactor formulas checked")

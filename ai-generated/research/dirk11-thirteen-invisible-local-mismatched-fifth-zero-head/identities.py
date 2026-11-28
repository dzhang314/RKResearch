"""Exact scalar bridge checks for the paid fifth and first next row."""
import sympy as S

b,x,e,lam,v,r,y,P0,delta,ell,rho,K=S.symbols(
    'b x e lambda v r y P0 delta ell rho K')
t=b-1
eta=e+lam*v
D=(1+lam)*y-lam
psi=lambda w:((4*r+3)*w-r)/(5*(2*r+3))
xi=-r/(10*(2*r+3))
L=(x-1)*ell-rho-v*K
Krel=((1+lam)*rho-lam*(x-1)*ell)/e
assert S.cancel((D*L-(y*(x-1)*ell-rho)).subs(K,Krel).subs(v,e*(1-y)/D))==0
assert S.cancel(D.subs(y,eta/(eta+v))-e/(eta+v))==0
assert S.cancel((psi(b)*eta+xi*b*v)*(eta+v)-t*eta**2-
                (eta+v)**2*(psi(b)*y+xi*b*(1-y)-t*y*y).subs(y,eta/(eta+v)))==0
assert S.cancel((y*t-(1-y)*(e+lam*t))-(D*t-e*(1-y)))==0
assert S.cancel(psi(1)-(3*r+3)/(5*(2*r+3)))==0
assert S.cancel(psi(b).subs(r,-1)+t/5)==0
# Optional reduced next companion identities; not needed for the paid repeats.
Wb=(1-y)*(e+lam*t)-t*y
V=e*(1-y)/D
f=t*(delta/e)*P0/(V-t)
kappa=V*(delta/e)*P0/(V-t)
assert S.cancel((V-t)-Wb/D)==0
assert S.cancel(f*Wb-t*delta*P0*D/e)==0
assert S.cancel(kappa*Wb-delta*(1-y)*P0)==0
print("Normalized fifth and next-row scalar identities exact")

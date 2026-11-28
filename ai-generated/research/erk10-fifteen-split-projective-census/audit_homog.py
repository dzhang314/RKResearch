"""Symbolic check of all outer/projective polynomial row scalings."""
import sympy as S
C,D,T,U,R,H,L,E,F,k,j,y=S.symbols("C D T U R H L E F k j y",nonzero=True)
c=C/D; tau=T/U; r=R/H
omega=210*c**3-336*c**2+168*c-28
Om=210*C**3-336*C*C*D+168*C*D*D-28*D**3
assert S.cancel(omega-Om/D**3)==0
assert S.cancel(U*D**3*(y*y-c*y+tau*(1+omega*y))-
 (U*D**3*y*y+(-U*C*D**2+T*Om)*y+T*D**3))==0
Ei,Fi=U*D**4*L*E,U*D**4*L*F
Ks,Js=D**2*H*L*k,D**4*H*L*j
K,Ll=tau*k,tau*(j-2*k/c)
factor=U*D**6*L*H
plain=[E*r*c*c-2*K*c,-E*r*c-E*c*c+F*c+2*K-Ll*c,-F*r*c*c+K*c*c]
scaled=[Ei*R*C*C-2*T*C*D**3*Ks,
        -Ei*R*C*D-Ei*H*C*C+Fi*H*C*D+4*T*D**4*Ks-T*C*D*Js,
        -Fi*R*C*C+T*C*C*D*D*Ks]
assert all(S.cancel(a-factor*b)==0 for a,b in zip(scaled,plain))
assert S.cancel(C*D**2*Ks-C*D**4*L*H*k)==0
assert S.cancel(C*Js-2*D**3*Ks-C*D**4*L*H*(j-2*k/c))==0
print("all projective outer and head-form common scales verified symbolically")

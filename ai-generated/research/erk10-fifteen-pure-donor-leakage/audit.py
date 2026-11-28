#!/usr/bin/env python3
"""Exact cofactor and marked-primitive algebra, without a clock search."""
import sympy as S
Y,a,d,e=S.symbols('Y a d e')
Q=S.Rational
t=3*a/2
nodes=(a,t,d,e)
def J(f):
    return sum(c*Y**(k+1)/(k+1) for (k,),c in S.Poly(f,Y).terms())
H=Y*(Y-a)*(Y-t)*(Y-d)
K=-Y**4/4+(a+t)*Y**3/3-a*t*Y**2/2
rho=lambda z:z*(3*z*z-10*a*z+9*a*a)/12
der=[S.factor(S.prod(z-w for w in nodes if w!=z)) for z in nodes]
C=[(d-t)*rho(a)*der[0],(a-d)*rho(t)*der[1],(t-a)*rho(d)*der[2],0]
def evt(f):
    q=S.cancel(J(f)/Y)
    return [S.factor(q.subs(Y,z)) for z in nodes]
M=S.Matrix([C,evt(H),evt(K)])
Z=[S.factor((-1)**i*M[:,[j for j in range(4) if i!=j]].det()) for i in range(4)]
common=a**5*(a-d)*(3*a-2*d)*(d-e)/3
Z=[S.factor(z/common) for z in Z]
assert S.expand(Z[2]+3*a**3*e*(a-e)*(3*a-2*e)*(15*a-11*e)/40960)==0
assert S.expand(Z[3]-3*a**3*d*(a-d)*(3*a-2*d)*(15*a-11*d)/40960)==0
T=[S.factor(z*x) for z,x in zip(Z,der)]
cards=[S.cancel((Y*S.prod(Y-u for u in (a,t,d) if u!=z))/
      (z*S.prod(z-u for u in (a,t,d) if u!=z))) for z in (a,t,d)]
J0=[S.factor(sum(w*u for w,u in zip(Z,evt(f)))) for f in cards]
G0=S.factor((t-a)*T[2]*J0[0]+d*(t-d)*T[0]*J0[2]/a)
G1=S.factor((t-a)*T[2]*J0[1]+d*(d-a)*T[1]*J0[2]/t)
g=a**4*d*e**2*(a-d)**2*(a-e)**2*(3*a-2*d)**2*(3*a-2*e)**2*(15*a-11*e)*(d-e)**2/1215
assert S.expand(G0+Q(6561,1342177280)*g)==0
assert S.expand(G1-Q(243,41943040)*g)==0
assert Q(243,41943040)*Q(1342177280,6561)==Q(32,27)
h,h_a=S.symbols('h h_a')
GAM_A=-Q(5,36)*a**4-2*a*h/9
GAM_T=-Q(3,16)*a**4
LAM_A=-a*h_a/2-Q(5,24)*a**4-2*a*h/9
LAM_T=-a*h/2-Q(9,32)*a**4
assert S.solve(GAM_A-Q(32,27)*GAM_T,h)==[3*a**3/8]
assert S.solve((LAM_A-Q(32,27)*LAM_T).subs(h,3*a**3/8),h_a)==[19*a**3/36]
assert S.cancel((19*a**3/36/a)/(3*a**3/8/t))==Q(19,9)
P=110*a*a-87*a*(d+e)+60*d*e
assert S.expand(19*T[0]-9*T[1]+9*a*d*e*(a-d)*(a-e)*(3*a-2*d)*(3*a-2*e)*(d-e)*P/81920)==0
S_A=42*a*a-27*a*(d+e)+16*d*e
S_T=117*a*a-63*a*(d+e)+31*d*e
N=17*a*a-15*a*(d+e)+11*d*e
assert S.cancel(sum(z*j/tt for z,j,tt in zip((a,t,d),J0,T))-18*N/(S_A*S_T))==0
assert S.expand(11*P-60*N-19*a*(10*a-3*(d+e)))==0
assert S.expand(15*P-87*N-57*(3*a*a-d*e))==0
assert S.expand((3*d-5*a)**2+2*a*a-(9*d*d-30*a*d+27*a*a))==0
print('common cofactor factor:',S.factor(common))
print('exceptional d/e cofactors:',Z[2],Z[3])
print('generic mean row scale:',S.factor(g))
print('generic mean equation: mean_a = 32/27 mean_t')
print('forced h_T = 3*a^3/8; forced h_A = 19*a^3/36')
print('T_t/T_a = 19/9 requires:',P)
print('nominal h primitive requires:',N)
print('elimination gives 3(d+e)=10a, de=3a^2, (3d-5a)^2+2a^2=0')

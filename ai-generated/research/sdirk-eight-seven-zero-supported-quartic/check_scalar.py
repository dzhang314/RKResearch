"""Independent exact scalar receipts for the supported early-quartic gate."""
import sympy as S

v,rho=S.symbols('v rho')
H=v**3-4*v*v-v+2
Q=4*v**3-12*v*v+3*v+2
k=1+2*v-v*v
N=[k-2*(1+v)**j+rho*(1+2*v)**j for j in range(3)]
a0=N[0]-N[1]
a1=2*N[1]-N[2]
c0=N[1]-(1+2*v)*N[0]
c1=N[2]-(1+2*v)*N[1]
assert S.expand(2*a0*c1-a1*c0-2*v*v*(rho*Q-H))==0
assert S.expand((676*v*v-1604*v-493)*H+(-169*v*v+570*v+525)*Q-64)==0
print('supported early-quartic determinant and integer Bezout verified')

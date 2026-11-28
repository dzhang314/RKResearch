import sympy as S
Y,a,d,e=S.symbols('Y a d e')
t=3*a/2
nodes=(a,t,d,e)
Q=S.Rational
def J(f):return sum(z*Y**(i+1)/(i+1)for (i,),z in S.Poly(f,Y).terms())
H=Y*(Y-a)*(Y-t)*(Y-d)
K=-Y**4/4+(a+t)*Y**3/3-a*t*Y**2/2
rho=lambda z:z*(3*z*z-10*a*z+9*a*a)/12
der=[S.factor(S.prod(z-w for w in nodes if w!=z))for z in nodes]
C=[S.factor(z)for z in ((d-t)*rho(a)*der[0],(a-d)*rho(t)*der[1],(t-a)*rho(d)*der[2],0)]
H0,H1=[[S.factor(S.cancel(J(g)/Y).subs(Y,z))for z in nodes]for g in (H,K)]
A=S.Matrix([C,H0,H1])
Z=[S.factor((-1)**i*A[:,[j for j in range(4)if j!=i]].det())for i in range(4)]
common=S.gcd_list(Z)
print("common",S.factor(common),flush=True)
Z=[S.cancel(z/common)for z in Z]
print('nullvector shapes',[(S.Poly(z,a,d,e).degree_list(),len(S.Poly(z,a,d,e).terms()))for z in Z],flush=True)
print('Z',*[S.factor(z)for z in Z],flush=True)
R0=-Q(5,36)*a**4
R1=-Q(3,16)*a**4
sigma=a*Y**3/9-a*a*Y**2/4
J0,J1=[[S.factor(S.cancel(J(g)/Y).subs(Y,z))for z in nodes] for g in (sigma,Y*(Y-a)*(Y-t))]
gden=(t-a)*Z[2]*der[2]
gnum=d*((t-d)*Z[0]*der[0]*R0/a+(d-a)*Z[1]*der[1]*R1/t)
row= S.factor(d*(d-a)*(d-t)*gden*sum(z*u for z,u in zip(Z,J0))+
             (gnum-gden*sigma.subs(Y,d))*sum(z*u for z,u in zip(Z,J1)))
print('blind third factor',row,flush=True)
assert S.expand(common-a**5*(a-d)*(3*a-2*d)*(d-e)/3)==0
assert S.expand(Z[2]+3*a**3*e*(a-e)*(3*a-2*e)*(15*a-11*e)/40960)==0
assert S.expand(Z[3]-3*a**3*d*(a-d)*(3*a-2*d)*(15*a-11*d)/40960)==0
want=-9*a**8*d**2*e**2*(a-d)**3*(a-e)**2*(3*a-2*d)**3*(3*a-2*e)**2*(15*a-11*e)*(d-e)**2/53687091200
assert S.expand(row-want)==0
assert S.factor(R0/a/rho(a))==-Q(5,6)
assert S.factor(R1/t/rho(t))==-Q(4,3)
assert Q(-9,53687091200)*55296*122880**2==-139968
assert S.expand((t*a*a/2-a**3/3)/(a*(t-a))-5*a/6)==0
print('all factor, ratio, and denominator-cleared identities checked exactly')

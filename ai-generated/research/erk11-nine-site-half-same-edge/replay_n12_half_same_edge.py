"""Half-half same extras, dormant physical 8: exact univariate centroid gates."""
import sympy as s
from sympy import QQ
from sympy.polys.rings import ring
from pathlib import Path
a=s.symbols('a')
R,aa=ring('a',QQ);X,x=ring('x',R)
bb=2-aa;dd=aa-1;hh=aa/2
W=x*x*(x-aa)**2*(1-x)**2*(x-dd)**2
def integral(f,j=0):
    return sum(v/(i[0]+j+1) for i,v in f.items())
I0,I1,I2=[integral(W,j) for j in range(3)]
JV=x**3*(6*x*x-15*aa*x+10*aa*aa)/30
Va=(1-x)**2*(x-dd)**2
H=integral(JV*Va);C=integral(JV*Va,1)
M=I1*H-I0*C;N=I2*H-I1*C
K=I2*H*H-2*C*H*I1+C*C*I0
P=(x-aa)*(x-hh)*(x-dd)*(H*x-C)
m=[integral(x*(1-x)*P,j) for j in range(5)]
E0,E1,E2,E3=[M*m[j+1]-N*m[j] for j in range(4)]
D=E0*E2-E1**2; U=E1*E2-E0*E3; V=E1*E3-E2**2
G0=E0*E3-E1*E2
T=lambda a:1-32*a+216*a*a-480*a**3+330*a**4
UC=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
MAT=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
Uab=sum(t*aa**i*bb**j for i,r in enumerate(UC) for j,t in enumerate(r))
L0=aa**2*D+aa*U+V; L1=-V
R0=dd**2*D+dd*U+V; R1=-D-U-V
Q=L0*R0+T(aa)*L1*R0+T(bb)*L0*R1+Uab*L1*R1
Dvec=[aa**5*N**(i+1)*M**(4-i)-aa**(i+1)*N**3*(6*N**2-15*aa*N*M+10*aa**2*M**2) for i in range(5)]
Rderb=[dd**j-(bb*j*dd**(j-1) if j else R.zero) for j in range(5)]
PhiR=[R0+R1*r for r in Rderb]
G=sum(Dvec[i]*MAT[i][j]*PhiR[j] for i in range(5) for j in range(5))
Amp=K*(N-hh*M)*(D*N*N+U*N*M+V*M*M)*M*M + (D*m[2]+U*m[1]+V*m[0])*N*(N-M)*(N-aa*M)*(N-dd*M)*(H*N-C*M)

assert H.gcd(C).degree()==0
assert M.gcd(N).degree()==0
assert D.gcd(U).gcd(V).degree()==0
assert Q.gcd(G)==aa*(aa-2)
assert [f.degree() for f in [H,M,D,Q]]==[4,8,30,68]
print('Exact Q[a] gcds: centroid 1/1; singular shifted minors 1; contacts a(a−2).')

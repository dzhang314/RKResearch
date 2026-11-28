"""Genuine dormant row 8, half-half with the same extras on both fronts."""
import sympy as s
from sympy import QQ
from sympy.polys.rings import ring
from pathlib import Path
a,v=s.symbols('a v')
R,aa,vv=ring('a,v',QQ); X,x=ring('x',R)
bb=2-aa;dd=aa-1;hh=aa/2
W=x*x*(x-aa)**2*(1-x)**2*(x-dd)**2
I=[sum(W.get((i,),R.zero)/(i+j+1) for i in range(9)) for j in range(3)]
I0,I1,I2=I
M=I1-vv*I0; N=I2-vv*I1
Ivv=I2-2*vv*I1+vv*vv*I0
P=(x-aa)*(x-hh)*(x-dd)*(x-vv)
m=[sum(P.get((i,),R.zero)/((i+j+2)*(i+j+3)) for i in range(5)) for j in range(5)]
e=[M*m[j+1]-N*m[j] for j in range(4)]
E0,E1,E2,E3=e
D=E0*E2-E1**2
U=E1*E2-E0*E3
V=E1*E3-E2**2
T=lambda a:1-32*a+216*a*a-480*a**3+330*a**4
UC=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
MAT=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
Uab=sum(t*aa**i*bb**j for i,r in enumerate(UC) for j,t in enumerate(r))
L0=aa**2*D+aa*U+V; L1=-V
R0=dd**2*D+dd*U+V; R1=-D-U-V
C=L0*R0+T(aa)*L1*R0+T(bb)*L0*R1+Uab*L1*R1
Dvec=[aa**5*N**(i+1)*M**(4-i)-aa**(i+1)*N**3*(6*N**2-15*aa*N*M+10*aa**2*M**2) for i in range(5)]
p1=(1-aa+1) # not used
Rder0=[R.one]*5
Rderb=[dd**j -(bb*j*dd**(j-1) if j else R.zero) for j in range(5)]
PhiR=[R0+R1*r for r in Rderb]
G=sum(Dvec[i]*MAT[i][j]*PhiR[j] for i in range(5) for j in range(5))
Amp=Ivv*(N-hh*M)*(D*N*N+U*N*M+V*M*M)*M*M + (D*m[2]+U*m[1]+V*m[0])*N*(N-M)*(N-aa*M)*(N-dd*M)*(N-vv*M)
guards=[aa,aa-1,aa-2,vv,vv-1,vv-aa,vv-dd,vv-hh,M,N,N-M,N-hh*M,N-dd*M,N-aa*M,N-vv*M,D]
def prim(q):return s.Poly(q.as_expr(),a,v).clear_denoms()[1].primitive()[1]
def strip(q,gs):
    assert q
    for u in gs:
        assert u
        while True:
            p,r=q.div(u)
            if r:break
            q=p
    return q
def residual(q):
    # Rational nonzero content only.
    return prim(strip(q,guards))

Ja=x**3*(6*x*x-15*aa*x+10*aa*aa)/30
Jb=(1-x)**3*(6*(1-x)**2-15*bb*(1-x)+10*bb*bb)/30
Vxa=x*x*(x-aa)**2; Vxb=(1-x)**2*(x-dd)**2
def it(f,j=0):return sum(z/(k[0]+j+1) for k,z in f.items())
H=it(Ja*Vxb); C1=it(Ja*Vxb,1); C2=it(Vxa*Jb,1); J0=it(Ja*Jb)
assert it(Vxa*Jb)==H
Lc=(C1-vv*H)*(C2-vv*H)-J0*Ivv
L0p=prim(strip(Lc,guards[:-1]))
E=[prim(strip(E,guards[:-1])) for E in [D,U,V]]
sres=[s.resultant(Ei.as_expr(),L0p.as_expr(),v) for Ei in E]
sg=s.gcd(s.gcd(*sres[:2]),sres[2])
print('central singular projections', [s.degree(f,a) for f in sres],[(s.degree(p,a),k) for p,k in s.factor_list(sg,a)[1]],flush=True)
C0,A0=map(residual,[C,Amp])
Q=[s.resultant(Ei.as_expr(),L0p.as_expr(),v) for Ei in [C0,A0]]
g=s.gcd(*Q)
print('central regular contact/support projections', [s.degree(f,a) for f in Q],
      [(s.degree(p,a),k) for p,k in s.factor_list(g,a)[1]],flush=True)



assert s.degree(I0.gcd(I1).gcd(I2).as_expr(),a)==0
variance=I0*I2-I1*I1
assert s.degree(variance.gcd((I0*C1-I1*H)*(I0*C2-I1*H)).as_expr(),a)==0
assert [s.degree(f,a) for f in sres]==[60,60,60] and s.degree(sg,a)==0
assert [s.degree(f,a) for f in Q]==[132,110] and s.degree(g,a)==0
print('Exact central half-half: no unordered centroid, singular, or regular residual fiber.')

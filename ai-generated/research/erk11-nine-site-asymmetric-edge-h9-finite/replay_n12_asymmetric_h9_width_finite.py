"""Exact finite width atlas, canonically asymmetric h@9 dormant edge."""
from sympy import QQ
from sympy.polys.rings import ring
from functools import reduce
from time import monotonic
import flint

N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
T4=[1,-32,216,-480,330]
U4=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
def integ(f,j=0):return sum(c/(i[0]+j+1) for i,c in f.items())
def ev(cs,q):return sum(c*q**i for i,c in enumerate(cs))
def dot(g,h):return sum(g[i]*N[i][j]*h[j] for i in range(5) for j in range(5))
def at(f,q):return sum(c*q**i[0] for i,c in f.items())

def model(R,a,b):
    W,X=ring('X',R)
    d=1-b;h=a/2;e=1-b/2
    V=X**2*(X-a)**2;Vr=(1-X)**2*(X-d)**2
    primitive=lambda f:sum(c*X**(i[0]+1)/(i[0]+1) for i,c in f.items())
    P=primitive(V)
    Q0=primitive(Vr);Q=W(sum(Q0.values()))-Q0
    H=integ(P*Vr);C1=integ(P*Vr,1);C2=integ(V*Q,1);J=integ(P*Q)
    I0,I1,I2=[integ(V*Vr,j) for j in range(3)]
    I=I2-(h+e)*I1+h*e*I0
    A=H*H-J*I0;B=J*I1-H*C1;C=J*I1-H*C2;D=C1*C2-J*I2
    Cmat=(C1-e*H)*(C2-h*H)-J*I
    Copp=(C1-h*H)*(C2-e*H)-J*I
    el=lambda c:[c**(i+1) for i in range(5)]
    er=lambda c:[(1-c)*c**i for i in range(5)]
    dl0=[R.one]+[R.zero]*4;dl1=[(i+1)*a**i for i in range(5)]
    dr0=[R.one]*5;dr1=[d**i-(b*i*d**(i-1) if i else 0) for i in range(5)]
    DX=[a**5*u-30*P*v for u,v in zip(el(X),el(a))]
    FX=[b**5*u-30*Q*v for u,v in zip(er(X),er(d))]
    Ks=[dot(DX,w).exquo(W(a)*X*(W(a)-X)) for w in [dr0,dr1]]
    Ms=[dot(w,FX).exquo(W(b)*(1-X)*(X-W(d))) for w in [dl0,dl1]]
    k0,k1=[at(f,h) for f in Ks]

    known=[a,b,a-1,a-2,b-1,b-2,a+b-1,a+b-2,2*a+b-2,a+2*b-2]
    return locals()
Gram = N

def data():
    R,va,vb,vz=ring('a,b,z',QQ);W=model(R,va,vb);X=W['X'];h0,d0,e0=[W[k] for k in ('h','d','e')]
    C=flint.fmpq_mpoly_ctx.get(('z','b','a'));z,b,a=C.gens();rd=lambda x:flint.fmpq(int(x.numerator),int(x.denominator))
    cv=lambda f:C.from_dict({(k,j,i):rd(v) for (i,j,k),v in f.items()})
    h,d,e,A,B0,C0,D0,H,J,C1,C2,I0,I1,I2=[cv(W[k]) for k in ('h','d','e','A','B','C','D','H','J','C1','C2','I0','I1','I2')]
    E=A*z+C0;N=-(B0*z+D0)
    P4=(X-va)*(X-h0)*(X-d0)*(X-e0);m=[cv(integ(X*(1-X)*P4,j)) for j in range(5)]
    M=[m[j+1]-z*m[j] for j in range(4)]
    D=M[0]*M[2]-M[1]*M[1];S=M[0]*M[3]-M[1]*M[2];P=M[1]*M[3]-M[2]*M[2]
    U=D*E;T=S*E-D*N
    Q=D*N*N-S*N*E+P*E*E
    R0=d*d*D-d*S+P;R1=-D+S-P
    L0=(a-e)*(a*U-T);L1=-e*T
    F=L0*R0+cv(ev(T4,va))*L1*R0+cv(ev(T4,vb))*L0*R1+cv(ev([ev(r,vb) for r in U4],va))*L1*R1
    K=lambda x,p,q:sum(cv(v)*p**j[0]*q**(3-j[0]) for j,v in x.items())
    G=R0*K(W['Ks'][0],z,C.constant(1))+R1*K(W['Ks'][1],z,C.constant(1))
    Mark=L0*K(W['Ms'][0],N,E)+L1*K(W['Ms'][1],N,E)
    Arow=[R0*cv(v)+R1*cv(w) for v,w in zip(W['dr0'],W['dr1'])];Aa=list(map(cv,W['el'](va)))
    Ra=sum(Aa[i]*Gram[i][j]*Arow[j] for i in range(5) for j in range(5))
    L=a*(C2-z*H)*(R0*K(W['Ks'][0],h,C.constant(1))+R1*K(W['Ks'][1],h,C.constant(1)))+30*h*(a-h)*(h-z)*J*Ra
    I=E*I2-(h*E+N)*I1+h*N*I0
    Om=m[0]*P-m[1]*S+m[2]*D;assert Om.degrees()[0]==0
    Support=I*(z-e)*(z*U-T)-Om*E*E*z*(1-z)*(z-a)*(z-d)
    guards=[cv(f) for f in W['known'][:10]]+[E,D,Om,I]+[z-u for u in [0,1,a,h,d,e]]
    guards += [N-u*E for u in (0,1,a,h,d,e,z)]+[T-u*U for u in (0,1,a,h,d,e,z)]+[N*U-E*T,S*S-4*D*P]
    raw={'F':F,'G':G,'R':Mark,'L':L,'Q':Q,'S':Support}
    for k,f in raw.items():
        for g in guards:
            while f:
                v=f.gcd(g)
                if v.is_constant(): break
                f=f//v
        raw[k]=f;print('gate',k,f.degrees(),flush=True)
    return raw,guards

def project(base='G',keys='QF'):
    D,G=data();C=flint.fmpq_mpoly_ctx.get(('b','a'));w=lambda f:C.from_dict({(j,i):v for (k,j,i),v in f.to_dict().items()})
    gs=[w(f) for f in G if not f.degrees()[0]];P={};t=monotonic()
    for k in keys:
        f=w(D[base].resultant(D[k],0))
        for g in gs:
            while f:
                d=f.gcd(g)
                if d.is_constant():break
                f=f//d
        P[k]=f
        print('width',base+k,f.degrees(),round(monotonic()-t,2),flush=True)
        if len(P)>1:
            u=reduce(lambda a,b:a.gcd(b),P.values());print('common',u.degrees(),[(g.degrees(),n) for g,n in u.factor()[1]],flush=True)
    return P


if __name__=='__main__':
    P=project()
    assert {k:f.degrees() for k,f in P.items()}=={'Q':(74,72),'F':(87,88)}
    assert P['Q'].gcd(P['F']).is_constant()
    print('Exact width projection gcd is a unit.',flush=True)

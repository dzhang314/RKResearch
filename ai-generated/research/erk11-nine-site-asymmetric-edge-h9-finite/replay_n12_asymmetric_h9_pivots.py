"""Exact affine and vertical dropout exclusions for the asymmetric h@9 dormant edge."""
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


def build(augmented=True):
    R,a,b,z=ring('a,b,z',QQ);B=model(R,a,b);X=B['X']
    h,e,d,H,I0,I1,I2,C1=[B[k] for k in ('h','e','d','H','I0','I1','I2','C1')]
    E=B['A']*h+B['B'];N=-(B['C']*h+B['D'])
    hull=(X-a)*(X-h)*(X-d)*(X-e)
    ms=[integ(X*(1-X)*hull,j) for j in range(5)]
    w=[ms[j+1]-z*ms[j] for j in range(4)]
    D=w[0]*w[2]-w[1]*w[1];SN=w[0]*w[3]-w[1]*w[2];PN=w[1]*w[3]-w[2]*w[2]
    R0=d*d*D-d*SN+PN;R1=-D+SN-PN
    Rrow=[R0*u+R1*v for u,v in zip(B['dr0'],B['dr1'])]
    Cx,T=ring('t',R)
    xx=lambda f:Cx(f)
    L0=xx(a-e)*(xx(a)-T);L1=-xx(e)*T
    G=L0*xx(R0)+xx(ev(T4,a))*L1*xx(R0)+xx(ev(T4,b))*L0*xx(R1)+xx(ev([ev(r,b) for r in U4],a))*L1*xx(R1)
    s=xx(SN)-xx(D)*T  # D times the other free clock s.
    Izs=xx(D*(I2-z*I1))+s*xx(z*I0-I1)
    u0=dot(B['el'](a),Rrow);kh=B['k0']*R0+B['k1']*R1
    L=xx(a*kh)*Izs+30*xx(h*(a-h)*(h-z)*u0)*(xx(C1*D)-s*xx(H))
    K=lambda p:sum(c*z**i[0] for i,c in p.items())
    Eport=K(B['Ks'][0])*R0+K(B['Ks'][1])*R1
    g0,g1=[G.get((j,),R.zero) for j in (0,1)]
    l0,l1=[L.get((j,),R.zero) for j in (0,1)]
    assert G.degree()==L.degree()==1
    mr=g1*l0-l1*g0
    f0=D*g0*g0+SN*g1*g0+PN*g1*g1
    f1=D*l0*l0+SN*l1*l0+PN*l1*l1
    Omega=ms[0]*PN-ms[1]*SN+ms[2]*D
    assert Omega.degrees()[2]==0
    p0,q0=I2-h*I1,h*I0-I1
    us=-(z-e)*(p0+q0*z)
    vs=(z-e)*(p0*z*D+q0*z*SN-q0*PN)-Omega*z*(1-z)*(z-a)*(z-d)
    sc=g1*vs-us*D*g0
    sn=vs*vs+SN*us*vs+D*PN*us*us
    guards=B['known'][:10]+[z,z-1,z-a,z-d,z-h,z-e,D,SN*SN-4*D*PN]+[D*y*y-SN*y+PN for y in (0,1,a,d,h,e,z)]
    res={'G':Eport,'R':mr,'F':f0,'Q':f1}
    if augmented:
        res.update({'S':sc,'T':sn});guards.append(Omega)
    return res,guards,E,N

def go():
    P,gu,E,N=build();R=E.ring;a,b,z=R.gens;W=model(R,a,b);X=W['X'];h,e,d,H,J,C2=[W[k] for k in ('h','e','d','H','J','C2')]
    E=W['A']*z+W['C'];N=-(W['B']*z+W['D'])
    P4=(X-a)*(X-h)*(X-d)*(X-e);m=[integ(X*(1-X)*P4,j) for j in range(5)];M=[m[j+1]-z*m[j] for j in range(4)]
    D=M[0]*M[2]-M[1]**2;S=M[0]*M[3]-M[1]*M[2];Phi=M[1]*M[3]-M[2]**2
    R0=d*d*D-d*S+Phi;R1=-D+S-Phi
    rr=[R0*p+R1*q for p,q in zip(W['dr0'],W['dr1'])];aa=W['el'](a)
    ra=sum(aa[i]*Gram[i][j]*rr[j] for i in range(5) for j in range(5))
    at=lambda f,w:sum(c*w**j[0] for j,c in f.items())
    P['L']=a*(C2-z*H)*(R0*at(W['Ks'][0],h)+R1*at(W['Ks'][1],h))+30*h*(a-h)*(h-z)*J*ra
    P['E']=E;P['N']=N
    R33=(ev([ev(v,b) for v in U4],a)-ev(T4,a)*ev(T4,b)).exquo(a*b)
    assert 633719116800000*(W['A']*W['D']-W['B']*W['C'])==-a*a*b*b*J*R33
    C=flint.fmpq_mpoly_ctx.get(('z','b','a'));Q=flint.fmpq_mpoly_ctx.get(('b','a'))
    cv=lambda f:C.from_dict({(k,j,i):flint.fmpq(int(v.numerator),int(v.denominator)) for (i,j,k),v in f.items()})
    w=lambda f:Q.from_dict({(j,i):v for (k,j,i),v in f.to_dict().items()});gg=list(map(cv,gu));Gw=[w(g) for g in gg if not g.degrees()[0]]
    def clean(f,guards):
        for g in guards:
            while f:
                v=f.gcd(g)
                if v.is_constant():break
                f=f//v
        return f
    P={k:clean(cv(f),gg) for k,f in P.items()};Cw={k:w(cv(f)) for k,f in [('J',J),('R33',R33)]}
    out={};t=monotonic()
    for x in 'EN':
        for k in 'GLFST':
            y=clean(w(P[x].resultant(P[k],0)),Gw);out[x+k]=y;print(x+k,y.degrees(),round(monotonic()-t,2),flush=True)
    for k,M in Cw.items():
        g=None
        for l,v in out.items():
            r=M.resultant(v,0);g=r if g is None else g.gcd(r);print(k,l,r.degrees(),g.degrees(),flush=True)
            if g.is_constant():break
        assert g.is_constant()
        print(k,'width exceptions',[(q.degrees()[1],n,q.to_dict() if q.degrees()[1]<=2 else '-') for q,n in g.factor()[1]],flush=True)



def vertical():
    P=project()
    assert {k:f.degrees() for k,f in P.items()}=={'Q':(74,72),'F':(87,88)}
    assert P['Q'].gcd(P['F']).is_constant()
    R,a,b=ring('a,b',QQ);B=model(R,a,b);C=flint.fmpq_mpoly_ctx.get(('b','a'))
    cv=lambda f:C.from_dict({(j,i):flint.fmpq(int(v.numerator),int(v.denominator))
                             for (i,j),v in f.items()})
    for pol,d in [(B['A']*B['e']+B['C'],(656,783)),(B['H'],(292,350))]:
        W=cv(pol)
        u,v=[W.resultant(f,0) for f in P.values()]
        assert (u.degrees()[1],v.degrees()[1])==d
        assert u.gcd(v).is_constant()
        print('vertical projection degrees',d,'gcd 1',flush=True)

if __name__=='__main__':
    go()
    vertical()

"""Exact asymmetric physical-8 slope-zero exclusion. Needs SymPy and python-flint."""
from sympy import QQ
from sympy.polys.rings import ring
from functools import reduce
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
def build():
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
    guards=B['known'][:10]+[z,z-1,z-a,z-d,z-h,z-e,D,SN*SN-4*D*PN]+[D*y*y-SN*y+PN for y in (0,1,a,d,h,e,z)]
    return {'G':Eport,'R':mr,'F':f0,'Q':f1},guards,E,N

def data():
    Q,G,E,N=build()
    C=flint.fmpq_mpoly_ctx.get(('z','b','a'))
    cv=lambda u:C.from_dict({(j,k,i):flint.fmpq(int(v.numerator),int(v.denominator)) for (i,k,j),v in u.items()})
    gu=list(map(cv,G))
    raw={}
    for k,f in Q.items():
        f=cv(f)
        # Remove live factors in the trivariate numerators before specialization.
        for g in gu:
            while not f%g:f=f//g
        raw[k]=f
    return raw,gu,cv(E),cv(N)



def certify():
    Z,guards,E,N=data()
    C=flint.fmpq_mpoly_ctx.get(('b','a'))
    def width(f):
        assert f and f.degrees()[0]==0
        return C.from_dict({(j,i):c for (k,j,i),c in f.to_dict().items()})
    gs=[width(g) for g in guards if g and not g.degrees()[0]]
    def clean(f):
        for g in gs:
            while True:
                h=f.gcd(g)
                if h.is_constant():break
                f=f//h
        return f
    E,N=map(lambda f:clean(width(f)),(E,N))
    H=clean(width(Z['G'].resultant(Z['F'],0)))
    assert [f.degrees() for f in (E,N,H)]==[(4,5),(4,3),(134,140)]
    F=E.resultant(N,0);G=E.resultant(H,0)
    assert [f.degrees() for f in (F,G)]==[(0,32),(0,1230)]
    assert F.gcd(G).is_constant()
    print('Exact affine-drop resultants degrees 32 and 1230; gcd 1.',flush=True)

if __name__=='__main__':
    certify()

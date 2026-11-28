"""Exact rational finite-clock atlas for opposite-half different-free nine-site ERK11.

Run with Python 3, sympy and python-flint. No modular projection is used.
"""
from functools import reduce
from sympy import QQ
from sympy.polys.rings import ring
import flint
T4=[1,-32,216,-480,330]
U4=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
def integ(f,j=0):return sum(c/(i[0]+j+1) for i,c in f.items())
def ev(cs,q):return sum(c*q**i for i,c in enumerate(cs))
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

    known=[a,b,a-1,a-2,b-1,b-2,a+b-1,a+b-2,2*a+b-2,a+2*b-2]
    return locals()

def build(pos,orient):
    R,a,b,z=ring('a,b,z',QQ);W=model(R,a,b);X=W['X']
    h,e,d,A,B,C,D,H,C1,C2,J,I0,I1,I2=[W[k] for k in ('h','e','d','A','B','C','D','H','C1','C2','J','I0','I1','I2')]
    P4=(X-a)*(X-h)*(X-e)*(X-d)
    ms=[integ(X*(1-X)*P4,j) for j in range(5)]
    m=[ms[j+1]-z*ms[j] for j in range(4)]
    D2=m[0]*m[2]-m[1]*m[1];SN=m[0]*m[3]-m[1]*m[2];PN=m[1]*m[3]-m[2]*m[2]
    fit=D2*X**2-SN*X+PN
    hull=P4*fit
    H3=ms[0]*PN-ms[1]*SN+ms[2]*D2
    assert H3.degrees()[2]==0 and H3==integ(X*(1-X)*hull)
    vv=lambda w:w*(1-w)*(a-w)*(w-d)
    jc=lambda w:-sum(c*w**j/((i[0]-j+1)*(i[0]-j+2)) for i,c in hull.items() for j in range(i[0]))
    cr=(vv(h)*((h-z)*jc(h)-H3)*(e-z)-vv(e)*((e-z)*jc(e)-H3)*(h-z)).exquo(h-e)
    assert sum(c*a**i*b**j*h**k for (i,j,k),c in cr.items())==vv(h)*H3
    Ta,Tb,U=ev(T4,a),ev(T4,b),ev([ev(row,b) for row in U4],a)
    W2,t,s=ring('t,s',R);cv=lambda a:W2(a)
    L0=cv(a-e)*(cv(a)-t);L1=-cv(e)*t
    R0=cv(h-d)*(s-cv(d));R1=-cv(1-h)*(1-s)
    F=L0*R0+cv(Ta)*L1*R0+cv(Tb)*L0*R1+cv(U)*L1*R1
    x,y=(t,s) if orient=='matched' else (s,t)
    P0=cv(A)*x*y+cv(B)*x+cv(C)*y+cv(D) if pos=='center' else cv(A*z+C)*y+cv(B*z+D)
    def row(f):
        dij=lambda i,j:f.get((i,j),0)
        return dij(1,0)-dij(0,1),D2*dij(0,0)+SN*dij(0,1)+PN*dij(1,1)
    Uf,Vf=row(F);Up,Vp=row(P0)
    resultant=Uf*Vp-Up*Vf
    norm=lambda u,v:v*v+SN*u*v+D2*PN*u*u
    NF,NP=norm(Uf,Vf),norm(Up,Vp)
    root=lambda w:D2*w*w-SN*w+PN
    guards=W['known'][:10]+[z,z-1,z-a,z-h,z-d,z-e,H3,D2,SN*SN-4*D2*PN]
    guards += [root(w) for w in (0,1,a,h,d,e,z)]
    return {'X':cr,'D':resultant,'F':NF,'B':NP,'G':Vf,'H':Vp},guards,(Uf,Vf,Up,Vp,D2,SN,PN)


def data(pos,orient):
    raw,gu,domain=build(pos,orient)
    C=flint.fmpq_mpoly_ctx.get(('z','b','a'))
    rv=lambda q:flint.fmpq(int(q.numerator),int(q.denominator))
    cv=lambda f:C.from_dict({(k,j,i):rv(v) for (i,j,k),v in f.items()})
    gs=list(map(cv,gu));out={}
    for k,v in raw.items():
        f=cv(v);log=[]
        for i,g in enumerate(gs):
            while f:
                c=f.gcd(g)
                if c.is_constant():break
                f=f//c;log.append((i,c.degrees()))
        out[k]=f;print(k,f.degrees(),log,flush=True)
    return out,gs,tuple(map(cv,domain))



def project(pos, orient):
    D,G,_=data(pos,orient)
    W=flint.fmpq_mpoly_ctx.get(('b','a'))
    def width(f):
        assert f and f.degrees()[0]==0
        return W.from_dict({(j,i):v for (k,j,i),v in f.to_dict().items()})
    guards=[width(f) for f in G if f and f.degrees()[0]==0]
    raw,clean={},{}
    for k in 'DFB':
        r=width(D['X'].resultant(D[k],'z'))
        raw[k]=r.degrees()
        for g in guards:
            while True:
                d=r.gcd(g)
                if d.is_constant():
                    break
                r=r//d
        clean[k]=r
    assert raw==({'D':(62,62),'F':(92,92),'B':(92,92)} if pos=='center'
                 else {'D':(69,69),'F':(92,92),'B':(76,76)})
    ds={k:f.degrees() for k,f in clean.items()}
    assert ds==({'D':(50,50),'F':(68,68),'B':(68,68)} if pos=='center'
                else {'D':(57,55),'F':(68,68),'B':(64,60)})
    assert clean['D'].gcd(clean['F']).is_constant()
    assert clean['D'].gcd(clean['B']).is_constant()
    print(pos,orient,'reduced width degrees (b,a)',ds,'both gcd = 1',flush=True)

if __name__=='__main__':
    for pos in ['center','edge']:
        for orient in ['matched','opposite']:
            project(pos,orient)

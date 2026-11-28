"""Exact characteristic-zero asymmetric opposite-center width-drop checks."""
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
def build(mode, raw_s=False):
    if raw_s:
        R,a,b,s=ring('a,b,s',QQ)
    else:
        R,a,b=ring('a,b',QQ)
    B=model(R,a,b);X=B['X']
    h,e,d=[B[k] for k in ('h','e','d')]
    A0,B0,C0,D0,H,C1,C2,I0,I1,I2=[B[k] for k in ('A','B','C','D','H','C1','C2','I0','I1','I2')]
    SN0,SD0=(-(h*B0+D0),h*A0+C0) if mode=='matched' else (-(h*C0+D0),h*A0+B0)
    SN,SD=(s,R.one) if raw_s else (SN0,SD0)
    HL=lambda f:sum(c*SN**j[0]*SD**(3-j[0]) for j,c in f.items())
    kn0,kn1=map(HL,B['Ms'])
    k0,k1=[B[k] for k in ('k0','k1')]
    P5=(X-a)*(X-h)*(X-d)*(X-e)*(SD*X-SN)
    m=[integ(X*(1-X)*P5,j) for j in range(4)]
    D2=m[0]*m[2]-m[1]*m[1]; D1=m[0]*m[3]-m[1]*m[2];D0m=m[1]*m[3]-m[2]*m[2]
    T,t,z=ring('t,z',R);cv=lambda a:T(a)
    L0=cv(a-e)*(cv(a)-t);L1=-cv(e)*t
    R0=(t-cv(d))*cv(SN-d*SD);R1=-(1-t)*cv(SD-SN)
    l=[L0*cv(x)+L1*cv(y) for x,y in zip(B['dl0'],B['dl1'])]
    r=[R0*cv(x)+R1*cv(y) for x,y in zip(B['dr0'],B['dr1'])]
    Ta,Tb,Uab=ev(T4,a),ev(T4,b),ev([ev(row,b) for row in U4],a)
    G=dot(l,r)
    aa,dd=[B[k](w) for k,w in [('el',a),('er',d)]]
    if mode=='matched':
        ML=cv(kn0)*L0+cv(kn1)*L1
        MR=cv(k0)*R0+cv(k1)*R1
    else:
        Ix=cv(SD*I2-SN*I1)+z*cv(SN*I0-SD*I1)
        Iy=cv(I2-h*I1)+z*cv(h*I0-I1)
        ML=cv(a)*Ix*(cv(k0)*R0+cv(k1)*R1)+30*cv(h*(a-h)*(h*SD-SN))*(cv(C1)-z*cv(H))*dot(list(map(cv,aa)),r)
        MR=cv(b)*Iy*(cv(kn0)*L0+cv(kn1)*L1)+30*cv((SD-SN)*(SN-d*SD)*(SN-h*SD))*(cv(C2)-z*cv(H))*dot(l,list(map(cv,dd)))
    term=lambda f,i,j:f.get((i,j),R.zero)
    f=lambda p:(term(p,1,0)-term(p,0,1),D2*term(p,0,0)+D1*term(p,0,1)+D0m*term(p,1,1))
    U_L,V_L=f(ML);U_R,V_R=f(MR)
    U_G=D2*term(G,1,0)+D1*term(G,2,0)
    V_G=D2*term(G,0,0)-D0m*term(G,2,0)
    RLR=U_L*V_R-U_R*V_L
    RLG=D2*U_L*V_G-U_G*V_L
    RRG=D2*U_R*V_G-U_G*V_R
    QL=V_L*V_L+D1*U_L*V_L+D0m*D2*U_L*U_L
    QR=V_R*V_R+D1*U_R*V_R+D0m*D2*U_R*U_R
    QG=D2*V_G*V_G+D1*U_G*V_G+D0m*U_G*U_G
    Kwidth=kn1*k1-Ta*kn0*k1-Tb*kn1*k0+Uab*kn0*k0
    nd=lambda x,y=1:D2*x*x-D1*x*y+D0m*y*y
    I=(SD*I2-(h*SD+SN)*I1+h*SN*I0)
    gu=[a,b,a-1,a-2,b-1,b-2,a+b-1,a+b-2,2*a+b-2,a+2*b-2,SD,SN,SN-SD,
        SN-a*SD,SN-h*SD,SN-d*SD,SN-e*SD,D2,I,D1*D1-4*D2*D0m,
        *[nd(x) for x in [0,1,a,h,d,e]],nd(SN,SD)]
    raw={'RLR':RLR,'RLG':RLG,'RRG':RRG,'QL':QL,'QR':QR,'QG':QG}
    if mode=='matched':raw['K']=Kwidth
    return raw,gu,SN0,SD0

def data(mode):
    R,G,N,D=build(mode)
    C=flint.fmpq_mpoly_ctx.get(('a','b'))
    cv=lambda f:C.from_dict({k:flint.fmpq(int(v.numerator),int(v.denominator)) for k,v in f.items()})
    guards=list(map(cv,G));out={}
    for na,f in R.items():
        f=cv(f);st=[]
        for i,p in enumerate(guards):
            while f:
                h=f.gcd(p)
                if h.is_constant():break
                f=f//h;st.append((i,h.degrees()))
        out[na]=f
        print(na,f.degrees(),st,flush=True)
    return out,guards,cv(N),cv(D)

def synth(mode):
    R,a,b=ring('a,b',QQ);B=model(R,a,b);P=(ev([ev(row,b) for row in U4],a)-ev(T4,a)*ev(T4,b)).exquo(a*b)
    C=flint.fmpq_mpoly_ctx.get(('a','b'))
    cv=lambda f:C.from_dict({k:flint.fmpq(int(v.numerator),int(v.denominator)) for k,v in f.items()})
    Q={k:cv(f) for k,f in [('R33',P),('H',B['H']),('J',B['J'])]}
    assert mode=='center'
    D,guards=data('opposite')[:2]
    uni=lambda f:flint.fmpq_poly([f.to_dict().get((i,0),0) for i in range(f.degrees()[0]+1)])
    names=('QG','RLR','RLG','RRG','QL','QR') if mode=='center' else ('G','F','R','Q')
    factors={k:reduce(lambda a,b:a.gcd(b),[uni(f.resultant(D[n],1)) for n in names]).factor()[1] for k,f in Q.items()}
    return Q,D,guards,names,factors

P=flint.fmpq_poly

def check(mode):
    Q,D,Gu,names,ff=synth(mode)
    assert {k:sorted((f.degree(),m) for f,m in row) for k,row in ff.items()}=={
      'R33':[(15,6)],'H':[(1,24),(2,2)],'J':[(1,24),(2,2),(6,6)]}
    a=P([0,1]);forbidden=a*(a-1)*(a-2)
    for nm,cands in ff.items():
        for F,m in cands:
            if not forbidden%F:
                print('forbidden a',nm,F,m,flush=True);continue
            tick=monotonic();F=F/F[F.degree()]
            def reduce(f):return f%F
            def inv(f):
                d,u,v=f.xgcd(F)
                assert d.degree()==0 and d[0]
                return reduce(u/d[0])
            def into(f):
                ds=f.to_dict();return [reduce(P([ds.get((i,j),0) for i in range(f.degrees()[0]+1)])) for j in range(f.degrees()[1]+1)]
            def trim(z):
                while z and not z[-1]:z.pop()
                return z
            def monic(f):
                f=trim(f)
                if not f:return f
                u=inv(f[-1]);return [reduce(v*u) for v in f]
            def rem(f,g):
                assert g and g[-1]==P([1]);d=len(g)-1
                f=trim(f[:]);
                if not d:return []
                while len(f)>d:
                    c=f[-1];shift=len(f)-len(g)
                    for j in range(d):f[j+shift]=reduce(f[j+shift]-c*g[j])
                    f.pop();trim(f)
                return f
            def gcd(f,g):
                f=monic(f);g=monic(g)
                while g:f,g=g,monic(rem(f,g))
                return f
            common=monic(into(Q[nm]));assert common
            print('checking exact',mode,nm,F.degree(),m,'initial b degree',len(common)-1,flush=True)
            for k in names:
                common=gcd(common,rem(into(D[k]),common));assert common
                print(' quotient',k,'degree',len(common)-1,round(monotonic()-tick,2),flush=True)
                if len(common)==1:break
            if len(common)>1:
                killed=[i for i,g in enumerate(Gu) if not rem(into(g),common)]
                print(' EXACT guarded coefficient fibers',len(common)-1,killed,'time',round(monotonic()-tick,2),flush=True)
                assert 10 in killed
            else:print(' EXACT no finite b',flush=True)


if __name__=='__main__':
    check('center')

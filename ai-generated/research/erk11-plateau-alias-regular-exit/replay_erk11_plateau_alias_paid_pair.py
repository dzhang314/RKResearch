"""Paid-pair witness for the degree-815 regular q10 n12 plateau alias (use --full to recover its exact factor)."""
import flint
from fractions import Fraction
from itertools import permutations
from functools import reduce
A=flint.fmpq_mpoly_ctx.get(('a','d','X'))
R=flint.fmpq_mpoly_ctx.get(('a','d'))
a,d,X=A.gens(); aa,dd=R.gens(); bb=1-dd
one=R.from_dict({(0,0):1});zero=R.from_dict({})
W=X**2*(X-a)**2;V=(1-X)**2*(X-d)**2
def prim(f):
 return A.from_dict({(i,j,k+1):c/(k+1) for (i,j,k),c in f.to_dict().items()})
def int_(f,s=0):
 r={}
 for (i,j,k),c in f.to_dict().items(): r[(i,j)]=r.get((i,j),0)+c/(k+s+1)
 return R.from_dict(r)
def intoA(f):
 return A.from_dict({(i,j,0):c for (i,j),c in f.to_dict().items()})
def at(f,y):
 return sum((R.from_dict({(i,j):c})*y**k for (i,j,k),c in f.to_dict().items()),zero)
P=prim(W);QQ=prim(V);Q=intoA(at(QQ,one))-QQ
H=int_(P*V);C1=int_(P*V,1);C2=int_(W*Q,1);J=int_(P*Q)
assert H==int_(W*Q) and J==C1-C2
I0,I1,I2=(int_(W*V,k) for k in range(3))
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
def dot(l,r):
 return sum((l[i]*N[i][j]*r[j] for i in range(5) for j in range(5)),zero)
EL=lambda t:[t**(i+1) for i in range(5)]
ER=lambda t:[(1-t)*t**i for i in range(5)]
L0=[one,zero,zero,zero,zero];La=[(i+1)*aa**i for i in range(5)]
R1=[one]*5;Rd=[dd**i-(bb*i*dd**(i-1) if i else zero) for i in range(5)]
def detGate(Lhat,Rhat):
 u,v=[dot(x,Rhat) for x in (L0,La)]
 w,z=[dot(Lhat,y) for y in (R1,Rd)]
 return dot([v*x-u*y for x,y in zip(L0,La)],[z*x-w*y for x,y in zip(R1,Rd)])
def atD():
 ZN=C1;ZD=H
 XN=I2*ZD-ZN*I1;XD=I1*ZD-ZN*I0
 U=C2*XD-XN*H
 pt=at(P,aa);pv=at(P,dd);vv=at(W,dd)
 DA=U*pt;NA=J*(dd*XD-XN)*vv-U*pv
 Lhat=[DA*x+NA*y for x,y in zip(EL(dd),EL(aa))]
 Rhat=ER(dd)
 return detGate(Lhat,Rhat),XN,XD,U,Lhat,Rhat
def atZero():
 ZN=I2*H-C2*I1;ZD=I1*H-C2*I0
 U=C1*ZD-ZN*H
 qt=at(Q,dd);qv=at(Q,zero);vv=at(V,zero)
 DA=U*qt;NA=-J*ZN*vv-U*qv
 Lhat=EL(aa)
 Rhat=[DA*x+NA*y for x,y in zip(ER(zero),ER(dd))]
 return detGate(Lhat,Rhat),ZN,ZD,U,Lhat,Rhat
def toQ(f,shape):
 qa=flint.fmpq_poly([0,1])
 out=flint.fmpq_poly([])
 for (i,j),c in f.to_dict().items():
  out += c*qa**i*shape(qa)**j
 return out
def diagonal_width(which):
    _,xn,xd,U,L,Rv=dict(d=atD,o=atZero)[which]()
    nz=(dd*xd-xn)*at(W,dd) if which=='d' else -xn*at(V,zero)
    raw=210*dot(L,Rv)-nz*at(P,aa)*at(Q,dd)
    dropped=[]
    for g in (aa,dd,dd-1,aa-dd):
        n=0
        while (raw%g).is_zero():
            raw=raw//g;n+=1
        dropped.append(n)
    expected=(8,13) if which=='d' else (10,8)
    assert raw.degrees()==expected
    return raw,tuple(dropped)


from time import monotonic

def col_gcd(vals):
    return reduce(lambda f,g:f.gcd(g),vals,zero)
def reduce_cols(l):
    g=col_gcd(l)
    assert g
    return [v//g for v in l],g
def coords(p,degree=None):
    n=p.degrees()[2] if degree is None else degree
    out=[{} for _ in range(n+1)]
    for (i,j,k),v in p.to_dict().items():out[k][(i,j)]=v
    return [R.from_dict(v) for v in out]
def hom3(p,n,d):
    assert p.degrees()[2]<=3
    return sum((v*n**j*d**(3-j) for j,v in enumerate(coords(p,3))),zero)
def det3(M):
    x,y,z=M
    return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])

def base(which):
    if which=='d':
        _,xn,xd,u,lh,rh=atD()
        zn,zd=C1,H
    else:
        _,zn,zd,u,lh,rh=atZero()
        xn,xd=C2,H
    if which=='d':
        T,RG=reduce_cols(rh)
        ls,LG2=reduce_cols([dot(v,T) for v in (L0,La)])
        Lx=[ls[1]*u-ls[0]*v for u,v in zip(L0,La)]
        L,LG=reduce_cols(Lx)
        rs,RG2=reduce_cols([dot(L,v) for v in (R1,Rd)])
    else:
        L,LG=reduce_cols(lh)
        rs,RG2=reduce_cols([dot(L,v) for v in (R1,Rd)])
        Tx=[rs[1]*u-rs[0]*v for u,v in zip(R1,Rd)]
        T,RG=reduce_cols(Tx)
        ls,LG2=reduce_cols([dot(v,T) for v in (L0,La)])
    print('Alias',which,'row divisors',LG.degrees(),RG.degrees(),
          'slope divisors',LG2.degrees(),RG2.degrees(),flush=True)
    return L,T,ls,rs,xn,xd,zn,zd,(LG,RG,LG2,RG2)

def model(which,left,base0):
    L,T,ls,rs,xn,xd,zn,zd,g0=base0
    if left:
        a0,c0=aa,dd
        l0,l1=ls;xn,xd=xn,xd
        mat=[sum((N[i][j]*T[j] for j in range(5)),zero) for i in range(5)]
        es=sum((intoA(mat[i])*X**(i+1) for i in range(5)),A.from_dict({}))
    else:
        a0,c0=1-dd,1-aa
        l0,l1=rs;xn,xd=zd-zn,zd
        mat=[sum((L[i]*N[i][j] for i in range(5)),zero) for j in range(5)]
        es=sum((intoA(mat[i])*X*(1-X)**i for i in range(5)),A.from_dict({}))
    aA=intoA(a0); cA=intoA(c0)
    es_a=at(es,a0)
    num=aA**5*es-X**3*(6*X**2-15*aA*X+10*aA**2)*intoA(es_a)
    E,r=divmod(num,X*(X-aA));assert r.is_zero()
    Eco,Egc=reduce_cols(coords(E,3))
    E=sum((intoA(c)*X**j for j,c in enumerate(Eco)),A.from_dict({}))
    E0=Eco[0]
    h=aA/2
    B0=X*(X-aA)*(X-h)
    B1=(X-h)*(aA*intoA(l0)-intoA(l0-l1)*X)
    S0,r=divmod(-aA*intoA(E0)*B0,X);assert r.is_zero()
    S1,r=divmod(aA*(E*intoA(at(B1,zero))-intoA(E0)*B1),X);assert r.is_zero()
    phi=X**2*(aA-X)
    p=[phi,X*B0,X*B1,B0,B1]
    weight=X*(1-X)*(X-aA)*(X-cA)
    ms=[[int_(weight*z,j) for z in p] for j in range(3)]
    N0=[r[:3] for r in ms]
    DT=det3(N0)
    nn=[]
    for j in (3,4):
        cont=[]
        for i in range(3):
            cont.append(-det3([[r[k] if k!=i else r[j] for k in range(3)] for r in ms]))
        nn.append(cont)
    oo=[hom3(v,xn,xd) for v in (aA*X*(X-aA)*intoA(E0),X*S0,X*S1,S0,S1)]
    GG=[sum((u*v for u,v in zip(C,oo[:3])),zero)+DT*oo[j] for C,j in zip(nn,(3,4))]
    GZ,gc=reduce_cols(GG)
    tnum,tden=-GZ[0],GZ[1]
    # These numerators share all width-scale transformations and retain
    # the projectivity of the true first-pool affine polynomial.
    v0=[v*tden+w*tnum for v,w in zip(*nn)]
    pp1=v0[2]*tden-v0[1]*tnum
    pp0=v0[0]*tnum-a0/2*pp1
    PW,PG=reduce_cols([pp0,pp1])
    qmod=sum((intoA(t)*z for t,z in zip(v0+[DT*tden,DT*tnum],p)),A.from_dict({}))
    print(' lside',left,'E scale',Egc.degrees(),'DT',DT.degrees(),
      'raw g',[v.degrees() for v in GG],'g gcd',gc.degrees(),'red g',[v.degrees() for v in GZ],
      'raw P',pp0.degrees(),pp1.degrees(),'P gcd',PG.degrees(),'red P',[v.degrees() for v in PW],flush=True)
    return {'pp':PW,'pg':PG,'tn':tnum,'td':tden,'dt':DT,'gc':gc,'qp':qmod,'es':Egc,'O':oo,'G':GG,'U':nn,
       'l0':l0,'l1':l1,'side':left}

def build(which):
    b=base(which)
    L=model(which,True,b);Z=model(which,False,b)
    p0,p1=L['pp'];q0,q1=Z['pp']
    G=p0*q1+p1*(q0+q1)
    D=diagonal_width(which)[0]
    print('Independent first line mark raw',G.degrees(), 'factor types',[(p.degrees(),n) for p,n in G.factor()[1]],flush=True)
    return D,G,L,Z,b
def rp(R0):
    assert R0.degrees()[1]==0
    a=R0.to_dict()
    return flint.fmpq_poly([a.get((k,0),0) for k in range(R0.degrees()[0]+1)])

def evp(f,av,prime=19):
    K=flint.fmpz_mod_poly_ctx(prime)
    c=[0]*(f.degrees()[1]+1)
    for (i,j),v in f.to_dict().items():
        c[j]=(c[j]+int(v.numerator)*pow(int(v.denominator),-1,prime)*pow(av,i,prime))%prime
    return K(c)

def geometry(a):
    assert not a.is_zero()
    for x in (aa,dd,dd-1,aa-dd):
        while (a%x).is_zero():a=a//x
    return a

def factor_815(D,G,path,full):
    import json
    expected=sorted((len(q)-1,n) for q,n in json.loads(path.read_text()))
    assert expected==[(1,16),(3,3),(8,8),(12,6),(12,7),(815,1)]
    co=next(q for q,n in json.loads(path.read_text()) if len(q)==816 and n==1)
    F=flint.fmpq_poly(list(map(flint.fmpq,co)))
    assert F.degree()==815
    if full:
        rr=rp(D.resultant(G,'d'))
        fac=rr.factor()[1]
        assert rr.degree()==1060
        assert sorted((q.degree(),n) for q,n in fac)==expected
        FF=next(q for q,n in fac if q.degree()==815)
        assert FF/FF[815]==F/F[815]
    return F

def verify(path,full):
    D,G,L,Z,b4=build('d')
    H0=factor_815(D,G,path,full)
    guard=[b4[2][0]*b4[-1][2],b4[3][0]*b4[-1][3],L['dt'],Z['dt'],L['G'][1],Z['G'][1]]
    p,a0=29,6
    C=flint.fmpz_mod_poly_ctx(p);X=C.gen();Y=1-X
    red=lambda c:int(c.numerator)*pow(int(c.denominator),-1,p)%p
    HH=C([red(q) for q in H0.coeffs()])
    assert HH.degree()==815 and HH(a0)==0 and HH.derivative()(a0)!=0
    D0=evp(D,a0,p); G0=evp(G,a0,p)
    assert D0.degree()==13
    assert D0.gcd(G0)==X-9
    ao=C([a0])[0];do=C([9])[0]
    one,zz=C([1])[0],C([0,1])[0]
    bo=one-do
    ev=lambda f:sum((red(c)*ao**i*do**j for (i,j),c in f.to_dict().items()),zz)
    assert all(c!=0 for c in (ao,bo,do,ao-do,ao-1,ev(H),ev(J),ev(b4[5])))
    assert all(ev(f)!=0 for f in guard)
    hh,er=ao/2,bo/2
    x,z=ev(b4[4])/ev(b4[5]),ev(C1)/ev(H)
    assert all(v!=0 for v in (do-x,ev(C2)-x*ev(H),ev(L['td']),ev(Z['td'])))
    tl,tr=ev(L['tn'])/ev(L['td']),ev(Z['tn'])/ev(Z['td'])
    ll0,ll1=ev(L['l0']),ev(L['l1']);rr0,rr1=ev(Z['l0']),ev(Z['l1'])
    dl=(X-hh)*(X*(X-ao)+tl*(ao*ll0-(ll0-ll1)*X))
    dr=(Y-er)*(Y*(Y-bo)+tr*(bo*rr0-(rr0-rr1)*Y))
    Ds=-(dl*dr*(X-x)*(X-z))
    assert Ds.degree()==8 and Ds[8]!=0 and Ds[8]==1
    P0=C([ev(f) for f in L['pp']])
    Q0=C([ev(f) for f in coords(L['qp'],4)])
    assert P0.degree()==1 and Q0.degree()==4
    assert all(c!=0 for c in (P0(hh),Q0(hh),Ds(ao),tl,tr))
    Q0=Q0*(P0(hh)*hh*hh*(ao-hh)/(ao*Q0(hh)))
    omega=X*(X-1)*(X-ao)*(X-do);Rp=omega*Q0
    M=C([sum((Rp[i]/(i-j) for i in range(j+1,9)),zz) for j in range(8)])
    V0=Ds*M%Q0;V1=P0*P0*X*(X-1)%Q0
    j=next(i for i in range(4) if V1[i]!=0)
    scale=-V0[j]/V1[j]
    assert scale!=0 and (V0+scale*V1).is_zero()
    PP,QQ=scale*P0,scale*Q0
    xi=-PP[0]/PP[1]
    assert Ds(xi)!=0
    lam=-QQ(xi)**2/Ds(xi)
    tau_poly,rem=divmod(QQ*QQ+lam*Ds,PP)
    assert rem.is_zero() and tau_poly.degree()<=7
    Dt=(ao-do)*Ds(ao)
    assert Dt!=0 and omega.derivative()(ao)!=0
    ell=(omega//(X-ao))/omega.derivative()(ao)
    inv0,ss,tt=((X-ao)*Q0).xgcd(Ds)
    assert inv0.degree()==0
    assert (ss*((X-ao)*Q0)+tt*Ds)==inv0
    bary=(P0*P0*X*(X-1)*ss)%Ds
    Bpool=sum((ell[i]/(i+1) for i in range(4)),zz)-scale*bary[7]/(inv0[0]*omega.derivative()(ao))
    nu,mu,tau=PP(ao)/Dt,QQ(ao)/Dt,tau_poly(ao)/Dt
    f=-ao*ao/2
    mark=(mu-f*nu)**2-(nu-f*Bpool)*(tau-f*mu)
    assert int(mark)==17
    print('Degree-815 width: at 29 a=6 is simple and full degree; width/line gcd exactly d-9.')
    print('Residue x,z =',int(x),int(z),'and ghost-fitted scale =',int(scale),'; used coefficient',j)
    print('Ordinary B_a, nu, mu, tau =',*(int(x) for x in (Bpool,nu,mu,tau)),'; known response =',int(f))
    print('Paid two-row compatibility residue:',int(mark))

if __name__=='__main__':
    import argparse
    from pathlib import Path
    p=argparse.ArgumentParser()
    p.add_argument('factor_data',type=Path)
    p.add_argument('--full',action='store_true')
    args=p.parse_args()
    verify(args.factor_data,args.full)

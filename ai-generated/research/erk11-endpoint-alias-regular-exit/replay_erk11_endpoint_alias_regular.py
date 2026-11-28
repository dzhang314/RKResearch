#!/usr/bin/env python3
"""Exact regular endpoint-alias width projection and all factor exits.
Requires python-flint 0.9+. No separate factor checkpoint.
"""
from itertools import combinations
from math import comb
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


qp=flint.fmpq_poly
def monic(f):
    return f/f[f.degree()]

def number_field(F):
    F=monic(F)
    qone=qp([1])
    qzero=qp()
    def trim(xs):
        while xs and xs[-1].is_zero():
            xs.pop()
        return xs
    def inv(x):
        r,s=F,x
        y,z=qzero,qone
        while not s.is_zero():
            h,v=divmod(r,s)
            r,s=s,v
            y,z=z,(y-h*z)%F
        assert r.degree()==0 and r[0]!=0
        return (y/r[0])%F
    def rem(f,g):
        out=f[:]
        i=inv(g[-1])
        while len(out)>=len(g):
            shift=len(out)-len(g)
            c=(out.pop()*i)%F
            for j in range(len(g)-1):
                out[shift+j]=(out[shift+j]-c*g[j])%F
            trim(out)
        return out
    def gcd(f,g):
        while g:
            f,g=g,rem(f,g)
        assert f
        c=inv(f[-1])
        return [(x*c)%F for x in f]
    def from_biv(f):
        c=f.to_dict()
        na,nd=f.degrees()
        return trim([qp([c.get((i,j),0) for i in range(na+1)])%F for j in range(nd+1)])
    def at_biv(f,v):
        z=qzero
        for u in reversed(from_biv(f)):
            z=(z*v+u)%F
        return z
    return from_biv,at_biv,gcd

def place(F,D,G,p,a0,d0):
    C=flint.fmpz_mod_poly_ctx(p)
    red=lambda q:int(q.numerator)*pow(int(q.denominator),-1,p)%p
    FH=C([red(q) for q in monic(F).coeffs()])
    assert FH.degree()==F.degree() and FH(a0)==0 and FH.derivative()(a0)!=0
    DD=evp(D,a0,p)
    assert DD.degree()==8
    gd=DD.gcd(evp(G,a0,p))
    assert gd.degree()==1 and -gd[0]/gd[1]==d0
    a=C([a0])[0]
    d=C([d0])[0]
    z=C([0])[0]
    def ev(f):
        return sum((red(q)*a**i*d**j for (i,j),q in f.to_dict().items()),z)
    return C,a,d,ev

def paid_large(F,D,G,L,Rm,bs):
    C,a,d,ev=place(F,D,G,37,34,15)
    w=1-d
    _,zn,zd,ui,lh,rh=atZero()
    sb=-zn*at(V,zero)
    guards=[aa,dd,dd-1,aa-dd,H,J,zd,ui,sb,bs[5],bs[2][0],bs[3][0],*bs[-1],
            L['es'],Rm['es'],L['dt'],Rm['dt'],L['G'][1],Rm['G'][1],
            L['td'],Rm['td'],L['tn'],Rm['tn'],L['gc'],Rm['gc'],L['pg'],Rm['pg']]
    assert all(ev(z)!=0 for z in guards)
    X=C.gen()
    Y=1-X
    zero0=C([0])[0]
    h=a/2
    k=w/2
    x=ev(bs[4])/ev(bs[5])
    z=ev(bs[6])/ev(bs[7])
    assert (x,z)==(4,28)
    tl=ev(L['tn'])/ev(L['td'])
    tr=ev(Rm['tn'])/ev(Rm['td'])
    l0,l1=ev(L['l0']),ev(L['l1'])
    r0,r1=ev(Rm['l0']),ev(Rm['l1'])
    BL=(X-h)*(X*(X-a)+tl*(a*l0-(l0-l1)*X))
    BR=(Y-k)*(Y*(Y-w)+tr*(w*r0-(r0-r1)*Y))
    Ds=-BL*BR*(X-x)*(X-z)
    assert Ds.degree()==8 and Ds[8]==1
    Q0=C([ev(t) for t in coords(L['qp'],4)])
    P0=C([ev(t) for t in L['pp']])
    assert Q0.degree()==4 and P0.degree()==1 and P0(h)!=0 and Q0(h)!=0
    Q0=Q0*(P0(h)*h*h*(a-h)/(a*Q0(h)))
    assert Q0.degree()==4
    Om=X*(X-1)*(X-a)*(X-d)
    q0=Om*Q0
    Mr=C([sum((q0[i]/(i-j) for i in range(j+1,q0.degree()+1)),zero0)
          for j in range(q0.degree())])
    A=Ds*Mr%Q0
    B=P0*P0*X*(X-1)%Q0
    assert B[0]!=0
    alpha=-A[0]/B[0]
    assert alpha==29 and (A+alpha*B).is_zero()
    P=alpha*P0
    Q=alpha*Q0
    xi=-P[0]/P[1]
    assert Ds(xi)!=0
    lamb=-Q(xi)**2/Ds(xi)
    Tb,rem=divmod(Q**2+lamb*Ds,P)
    assert rem.is_zero()
    assert a!=1 and Om.derivative()(a)!=0 and Ds(a)!=0
    ell=(Om//(X-a))/Om.derivative()(a)
    g,inv,_=((X-a)*Q0).xgcd(Ds)
    assert g.degree()==0 and g[0]!=0
    b0=(P0*P0*X*(X-1)*inv)%Ds
    mass=sum((ell[i]/(i+1) for i in range(4)),zero0)-alpha*b0[7]/(g[0]*Om.derivative()(a))
    dpa=(a-d)*Ds(a)
    nu,m2,m3=P(a)/dpa,Q(a)/dpa,Tb(a)/dpa
    f=-a*a/2
    mark=(m2-f*nu)**2-(nu-f*mass)*(m3-f*m2)
    assert (mass,nu,m2,m3,f,mark)==(14,16,29,36,14,26)
    print('degree 625: simple (37,34,15), x,z=4,28, scale=29; '
          'left paid pair tuple (14,16,29,36,14), mark=26')

def replay():
    D,G,L,Rm,bs=build('o')
    assert D.degrees()==(10,8) and G.degrees()==(56,48) and D.gcd(G).total_degree()==0
    assert [f.degrees() for f in L['pp']]==[(30,23)]*2
    assert [f.degrees() for f in Rm['pp']]==[(26,25)]*2
    raw=[bs[2][0]*bs[-1][2],bs[3][0]*bs[-1][3],L['dt'],Rm['dt'],L['G'][1],Rm['G'][1]]
    cuts=list(map(geometry,raw))
    DD=evp(D,6)
    assert DD.degree()==8
    assert all(DD.gcd(evp(f,6)).degree()==0 for f in [G,*cuts])
    refl=lambda c:[sum(((-1)**i*comb(j,i)*c[j] for j in range(i,len(c))),zero)
                   for i in range(len(c))]
    ql,_=reduce_cols(coords(L['qp'],4))
    qr,_=reduce_cols(refl(coords(Rm['qp'],4)))
    assert all((ql[i]*qr[j]-ql[j]*qr[i]).is_zero() for i,j in combinations(range(5),2))
    print('endpoint D and independent first-pool mark bidegrees (10,8),(56,48); '
          'all ten second-pool minors identically zero')
    print('coefficient a=6 mod19: D degree8, unit gcd against projective mark and six raw mask equations')
    # None of the width equations has an identically zero vertical fiber over Qbar.
    dco=D.to_dict()
    def co(i):
        return qp([dco.get((j,i),0) for j in range(D.degrees()[0]+1)])
    assert reduce(lambda f,g:f.gcd(g),(co(i) for i in range(9)),qp()).degree()==0
    res=rp(D.resultant(G,'d'))
    assert res.degree()==922
    fs=res.factor()[1]
    pat=sorted((f.degree(),m) for f,m in fs)
    assert pat==[(1,9),(4,1),(4,3),(4,22),(8,8),(12,7),(36,1),(625,1)]
    fs={(f.degree(),m):monic(f) for f,m in fs}
    print('regular exact projection degree 922, irreducible factors:',pat)
    assert fs[(1,9)]==qp([0,1])
    print('degree 1: a=0')
    # A true leading-degree drop: the two specialized d-polynomials have no common root.
    F=fs[(4,3)]
    assert F==monic(qp([1,-14,56,-84,42]))
    c,_,gcd=number_field(F)
    D0,G0=c(D),c(G)
    assert (len(D0)-1,len(G0)-1)==(7,45) and gcd(D0,G0)==[qp([1])]
    print('quartic power 3: actual d degrees 7,45; exact gcd 1')
    F=fs[(4,22)]
    assert F==monic(qp([1,-16,72,-120,66]))
    c,_,_=number_field(F)
    assert not c(raw[1])
    print('quartic power 22: right raw initial slope zero for all d')
    _,zn,zd,_,_,_=atZero()
    migrations=[
        ((4,1),dd,(17,14,0),'d=0'),
        ((8,8),H,(17,8,7),'H=0'),
        ((12,7),zd,(23,20,19),'z_D=0'),
        ((36,1),zn,(23,2,6),'z_N=0')
    ]
    for typ,mask,witness,msg in migrations:
        F=fs[typ]
        c,e,gcd=number_field(F)
        g=gcd(c(D),c(mask))
        assert len(g)==2 and g[1]==qp([1])
        d0=-g[0]
        assert all(e(j,d0).is_zero() for j in (D,G,mask))
        place(F,D,G,*witness)
        print('factor',typ,': exact shared d root has',msg,
              '; whole D/mark residue gcd linear at',witness)
    paid_large(fs[(625,1)],D,G,L,Rm,bs)
    print('entire regular endpoint alias excluded; all six raw mask loci retained')
    print('six exact exceptional projection degrees:',
          [rp(D.resultant(g,'d')).degree() for g in cuts])

if __name__=='__main__':
    replay()

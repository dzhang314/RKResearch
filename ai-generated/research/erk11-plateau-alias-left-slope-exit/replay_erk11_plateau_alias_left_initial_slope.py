"""Exact rational-field exit for the left initial slope mask of the plateau-alias chart."""
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

QP=flint.fmpq_poly
from itertools import combinations

def exactfield(H):
    H=H/H[H.degree()]
    unit=QP([1]);zero=QP();av=QP([0,1])
    def trim(w):
        while w and w[-1].is_zero():w.pop()
        return w
    def inv(x):
        s,t=x,H;u,v=unit,zero
        while t:
            q,r=divmod(s,t);s,t=t,r;u,v=v,(u-q*v)%H
        assert s.degree()==0 and s[0]!=0
        return (u/s[0])%H
    def monic(g):
        if not g:return g
        v=inv(g[-1]);return [(t*v)%H for t in g]
    def rem(f,g):
        f=f[:];w=inv(g[-1])
        while len(f)>=len(g):
            s=len(f)-len(g);c=(f[-1]*w)%H
            for i in range(len(g)-1):f[i+s]=(f[i+s]-c*g[i])%H
            f.pop();trim(f)
        return f
    def quotient(f,g):
        f=f[:];q=[zero]*(len(f)-len(g)+1);w=inv(g[-1])
        while len(f)>=len(g):
            j=len(f)-len(g);c=(f[-1]*w)%H;q[j]=c
            for i in range(len(g)-1):f[i+j]=(f[i+j]-c*g[i])%H
            f.pop();trim(f)
        assert not f
        return trim(q)
    def gcd(f,g):
        while g:f,g=g,rem(f,g)
        return monic(f)
    def at(f):
        B=f.to_dict();ad,bd=f.degrees()
        return trim([QP([B.get((i,j),0) for i in range(ad+1)])%H for j in range(bd+1)])
    def linear(g):
        assert len(g)==2 and g[1]==unit
        return -g[0]
    def spec(f,dv):
        r=zero
        for t in reversed(at(f)):r=(r*dv+t)%H
        return r
    return at,gcd,inv,linear,spec,quotient

def replay():
 D,_=diagonal_width('d');_,xn,xd,U,hL,hR=atD()
 Rt,_=reduce_cols(hR)
 ol0,ol1=map(geometry,[dot(v,Rt) for v in (L0,La)])
 p0=rp(D.resultant(ol0,'d'));p1=rp(D.resultant(ol1,'d'))
 assert [p0.degree(),p1.degree()]==[32,80]
 g=p0.gcd(p1); fs=g.factor()[1]
 assert g.degree()==16 and sorted((f.degree(),m) for f,m in fs)==[(1,4),(12,1)]
 assert next(f for f,m in fs if f.degree()==1)[0]==0
 F=next(f for f,m in fs if f.degree()==12)
 coeff=[72,-3456,71496,-841392,6277059,-31362048,108028376,-259591392,
        433718388,-493307520,363884400,-156816000,29947500]
 assert F/F[12]==QP(coeff)/coeff[-1]
 at0,gg,iv,ln,sp,quo=exactfield(F)
 ds=ln(gg(at0(D),gg(at0(ol0),at0(ol1))))
 assert all(sp(f,ds).is_zero() for f in (D,ol0,ol1))
 assert all(not sp(f,ds).is_zero() for f in (aa,dd,1-dd,aa-dd,H,J,xd,U,dd*xd-xn))
 print('Exact left-mask widths: two resultants of degrees 32 and 80; a^4 times irreducible degree 12; common d-gcd linear.',flush=True)

 # Right opposing row is the actual central L9. Obtain the actual R11
 # direction from its off-diagonal. Left now uses that different row.
 L,LG=reduce_cols(hL)
 rs,RG=reduce_cols([dot(L,v) for v in (R1,Rd)])
 Rv=[rs[1]*v-rs[0]*w for v,w in zip(R1,Rd)]
 T,TG=reduce_cols(Rv)
 ls,SG=reduce_cols([dot(u,T) for u in (L0,La)])
 assert all(not sp(f,ds).is_zero() for f in rs+ls+[LG,RG,TG,SG])
 b=(L,T,ls,rs,xn,xd,C1,H,(LG,TG,SG,RG))
 A=model('d',True,b);B=model('d',False,b)
 guards=[A['dt'],B['dt'],A['G'][1],B['G'][1],A['td'],B['td'],A['tn'],B['tn'],
         A['pg'],B['pg'],A['es'],B['es'],A['gc'],B['gc']]
 assert all(not sp(f,ds).is_zero() for f in guards)
 p0,p1=A['pp'];q0,q1=B['pp']
 pi=p0*q1+p1*(q0+q1)
 rem=sp(pi,ds)
 assert rem.degree()==11
 print('Actual L9 and alternate R11 give live slope and independent outer matches; all rotated moment/affine guards live.',flush=True)
 print('The required first-pool line determinant is a nonzero degree-11 residue in the exact degree-12 width field.',flush=True)
if __name__=='__main__':
 replay()

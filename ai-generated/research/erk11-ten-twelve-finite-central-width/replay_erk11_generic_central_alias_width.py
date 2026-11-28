"""Exact coefficient specialization for the q10 n12 central alias finite-width theorem."""
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

def kernel(rows,n):
    w=[r[:] for r in rows];pi=[];ip=0
    for j in range(n):
        m=next((k for k in range(ip,len(w)) if w[k][j]!=0),None)
        if m is None:continue
        w[ip],w[m]=w[m],w[ip]; d=w[ip][j]
        w[ip]=[r/d for r in w[ip]]
        for k in range(len(w)):
            if k!=ip and w[k][j]!=0:
                x=w[k][j];w[k]=[u-x*v for u,v in zip(w[k],w[ip])]
        pi.append(j);ip+=1
    if ip!=n-1:return ip,None
    free=next(j for j in range(n) if j not in pi)
    v=[0]*n;v[free]=1
    for i,j in enumerate(pi):v[j]=-w[i][free]
    return ip,v
def fiber(p,K,aval,dval,which):
    Fp=flint.fq_default_poly_ctx(K); t=Fp.gen()
    oo,one=K.zero(),K.one()
    # Shadowed labels are literal widths, not response coefficients.
    a=aval;d=dval;b=1-d;h=a/2;e=(1+d)/2
    red=lambda c:int(c.numerator)*pow(int(c.denominator),-1,p)%p
    ev=lambda r:sum((K(red(c))*a**i*d**j for (i,j),c in r.to_dict().items()),oo)
    El=lambda y:[y**(i+1) for i in range(5)]
    Er=lambda y:[(1-y)*y**i for i in range(5)]
    L0=[one,oo,oo,oo,oo];La=[(i+1)*a**i for i in range(5)]
    R0=[one]*5;Rd=[d**i-(b*i*d**(i-1) if i else oo) for i in range(5)]
    Pr=lambda y:y**3*(6*y*y-15*a*y+10*a*a)/30
    Qr=lambda y:(1-y)**3*(6*(1-y)**2-15*b*(1-y)+10*b*b)/30
    Lf=lambda y:y*y*(a-y)/a
    Rf=lambda y:(1-y)**2*(y-d)/b
    dot=lambda l,r:sum((l[i]*N[i][j]*r[j] for i in range(5) for j in range(5)),0)
    linc=lambda A,B,u,v:[u*x+v*y for x,y in zip(A,B)]
    assert all(q!=0 for q in (a,d,a-d,b))
    hh,c1,c2,j0,i0,i1,i2=map(ev,(H,C1,C2,J,I0,I1,I2))
    assert hh!=0 and j0!=0
    if which=='d':
        z=c1/hh
        xd=i1-z*i0
        assert xd!=0
        x=(i2-z*i1)/xd
        U=c2-x*hh
        assert U!=0 and x!=d
        p9=j0*(d-x)*d*d*(d-a)**2/U
        l9=linc(El(d),El(a),one,(p9-Pr(d))/Pr(a))
        r9=Er(d)
    else:
        x=c2/hh
        zd=i1-x*i0
        assert zd!=0
        z=(i2-x*i1)/zd
        U=c1-z*hh
        assert U!=0 and z!=0
        r9_= -j0*z*d*d/U
        l9=El(a)
        r9=linc(Er(oo),Er(d),one,(r9_-Qr(oo))/Qr(d))
    lA,lB=dot(L0,r9),dot(La,r9)
    rA,rB=dot(l9,R0),dot(l9,Rd)
    assert all(c!=0 for c in (lA,lB,rA,rB))
    lp=linc(L0,La,lB,-lA);rp=linc(R0,Rd,rB,-rA)
    assert dot(lp,rp)==0
    def fromL(y):return linc(El(y),El(a),Pr(a),-Pr(y))
    def fromR(y):return linc(Er(y),Er(d),Qr(d),-Qr(y))
    def marking(clock,half,plateau,base,fromD,left):
        dm=fromD(clock)
        eh=fromD(half);et=fromD(t)
        Et=linc(eh,et,-(clock-plateau)*(clock-t)*(t-plateau)*base(t),
                     (clock-plateau)*(clock-half)*(half-plateau)*base(half))
        if left:
            f0,f1=dot(dm,r9),dot(dm,rp)
            g0,g1=dot(Et,r9),dot(Et,rp)
            d0=oo
        else:
            f0,f1=dot(l9,dm),dot(lp,dm)
            g0,g1=dot(l9,Et),dot(lp,Et)
            d0=one
        G=f0*g1-f1*g0
        C=(t-d0)*(t-plateau)*(t-half)
        assert (G%C).is_zero()
        gg=G//C
        return gg,dm,Et,f0,f1,g0,g1
    PL,dx,ex,fL,hL,gL,kL=marking(x,h,a,Lf,fromL,True)
    PR,dz,ez,fR,hR,gR,kR=marking(z,e,d,Rf,fromR,False)
    wi=t*(1-t)*(t-a)*(t-d)
    mom=lambda j,m: sum((wi[i]/(i+j+m+1) for i in range(5)),oo)
    mo=[[mom(j,m) for m in range(5)] for j in range(3)]
    def det4(rows):
        out=Fp.zero()
        for ix in permutations(range(4)):
            v=Fp.one()
            for i,j in enumerate(ix): v*=rows[i][j]
            if sum(ix[i]>ix[j] for i in range(4) for j in range(i+1,4))%2:out-=v
            else:out+=v
        return out
    def flank(clock,half,plateau,other0,base,f0,f1,g0,g1,l0,l1,is_left):
        if is_left:
            de=l0*(a-t)+l1*t; nu=l0*a*(a-t)
            cbase=[oo,oo,one,-1/a]
        else:
            de=l0*(t-d)+l1*(1-t);nu=l0*(t-d)*d+l1*(1-t)
            cbase=[-d/b,(1+2*d)/b,-(2+d)/b,1/b]
        cb=[-nu*half*t, de*half*t+nu*(half+t),-de*(half+t)-nu,de]
        prod=(t-other0)*(t-plateau)*(t-half)
        delta=(half-plateau)*(t-plateau)*(half-t)*base(half)*base(t)
        assert (g0%prod).is_zero() and (g1%prod).is_zero() and (delta%prod).is_zero()
        g0,g1,delta=[g//prod for g in (g0,g1,delta)]
        rows=[[sum((coeff[k]*row[k+s] for k in range(4)),0) for coeff,s in ((cbase,0),(cbase,1),(cb,0),(cb,1))]
              for row in mo]
        bv=sum((cb[j]*clock**j for j in range(4)),Fp.zero())
        extras=[]
        for f,g in [(f0,g0),(f1,g1)]:
            A=base(clock)*g+delta*f
            B=bv*g
            extras.append([A,clock*A,B,clock*B])
        dets=[det4(rows+[q]) for q in extras]
        return dets,rows,extras,cb,cbase
    PL,ML,EL_,BL,Lb=flank(x,h,a,oo,Lf,fL,hL,gL,kL,lA,lB,True)
    PR,MR,ER_,BR,Rb=flank(z,e,d,one,Rf,fR,hR,gR,kR,rA,rB,False)
    VLside=t*(t-a); VRside=(t-1)*(t-d)
    assert all((r%v).is_zero() for vv,v in [(PL,VLside),(PR,VRside)] for r in vv)
    PL=[g//VLside for g in PL]; PR=[g//VRside for g in PR]
    # Fixed column-0 determinant uniformly monic after its leading unit.
    assert [g.degree() for g in PL+PR]==[4,4,4,4]
    gl=PL[0].gcd(PL[1]);gr=PR[0].gcd(PR[1])
    Ls,Rs=gl.roots(),gr.roots()
    assert gl.degree()==gr.degree()==4
    assert len(Ls)==len(Rs)==4 and all(m==1 for _,m in Ls+Rs)
    st=[]
    for u,_ in Ls:
        for v,_ in Rs:
            m1=[p(u) if hasattr(p,'degree') else p for p in BL]
            m2=[p(v) if hasattr(p,'degree') else p for p in BR]
            rows=[[p(u) if hasattr(p,'degree') else p for p in row]+[oo]*4 for row in ML+EL_]
            rows+=[[oo]*4+[p(v) if hasattr(p,'degree') else p for p in row] for row in ER_]
            prev=lambda q,i:q[i] if i in (0,1,2,3) else oo
            for i in range(5):
                co=[prev(q,i-s) for q in (Lb,m1,Rb,m2) for s in (0,1)]
                rows.append(co[:4]+[-x for x in co[4:]])
            rk,w=kernel(rows,8)
            if rk==8:
                st.append(8)
            else:
                assert rk==7 and w is not None
                assert w[0]*w[5]-w[1]*w[4]!=0
                st.append(7)
    assert len(st)==16
    return st


def replay():
    assert all(sum((Fraction(210*N[k][j],(i+k+2)*(i+k+3)) for k in range(5)),Fraction(0))==int(i==j)
               for i in range(5) for j in range(5))
    for which,aval,deg in (('d',2,(4,9)),('o',6,(2,3,3))):
        D,dropped=diagonal_width(which)
        Aoff=dict(d=atD,o=atZero)[which]()[0]
        assert (Aoff%D).is_zero()
        # Coefficient gcd certifies no vertical all-d fiber over any
        # characteristic-zero extension, including exceptional widths.
        DD=D.to_dict()
        c=[flint.fmpq_poly([DD.get((i,j),0) for i in range(D.degrees()[0]+1)])
           for j in range(D.degrees()[1]+1)]
        assert reduce(lambda f,g:f.gcd(g),c).degree()==0
        print(which,'width bidegree',D.degrees(),'guard powers',dropped,
              'coefficient gcd 1; outer derivative width contact is a multiple',flush=True)
        p=19;C=flint.fmpz_mod_poly_ctx(p)
        assert all(int(v.denominator)%p!=0 for z in (D,H,C1,C2,J,I0,I1,I2,P,Q,W,V)
                   for v in z.to_dict().values())
        red=lambda c:int(c.numerator)*pow(int(c.denominator),-1,p)%p
        M=C([red(f(aval)) for f in c])
        fs=M.factor()[1]
        assert M.degree()==D.degrees()[1] and sorted((f.degree(),m) for f,m in fs)==[(d,1) for d in deg]
        cnt={8:0,7:0}
        for f,_ in fs:
            K=flint.fq_default_ctx(p,2*f.degree(),'k',fq_type='FQ_NMOD')
            F=flint.fq_default_poly_ctx(K)
            roots=F([int(c) for c in f.coeffs()]).roots()
            assert len(roots)==f.degree() and all(m==1 for _,m in roots)
            for k in fiber(p,K,K(aval),roots[0][0],which):
                cnt[k]+=1
        print(which,'at a =',aval,'mod 19; d factor degrees',deg,
              'full flank quartics; rank8:',cnt[8],'; rank7 with nonproportional P:',cnt[7],flush=True)
    print('Both exact specializations give a unit ideal in the finite-free atlas.',flush=True)

if __name__=='__main__':
    replay()

"""Complete exact edge-dormant half-half different-extra exit.
Requires SymPy and python-flint (verified 0.9). All computations use
exact coefficients: certified integer CRT resultants and unit lifts
only in complete algebraic coefficient quotients.
"""
import flint
import sympy as sy
from sympy import QQ
from sympy.polys.rings import ring
from functools import reduce
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
T4=[1,-32,216,-480,330]
U4=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
def ev(cs,q):return sum(c*q**i for i,c in enumerate(cs))
def dot(g,h):return sum(g[i]*N[i][j]*h[j] for i in range(5) for j in range(5))
def integ(f,j=0):return sum(c/(q[0]+j+1) for q,c in f.items())
def at(f,z):return sum(c*z**q[0] for q,c in f.items())
def hom(f,z,zD):
    n=f.degree()
    return sum(T(c)*z**i[0]*zD**(n-i[0]) for i,c in f.items())
def common_model(K):
    ar,a0=ring('a',K)
    global T
    T,x=ring('x',ar)
    W,X=ring('X',T)
    a=T(a0); b=2-a; h=a/2; d=a-1
    V=X**2*(X-a)**2
    U=(1-X)**2*(X-d)**2
    prim=lambda f:sum(c*X**(q[0]+1)/(q[0]+1) for q,c in f.items())
    P=prim(V)
    _Q=prim(U)
    Q=W(sum(_Q.values()))-_Q
    H=integ(P*U);C1=integ(P*U,1);C2=integ(V*Q,1);J=integ(P*Q)
    I0,I1,I2=[integ(V*U,j) for j in range(3)]
    A=H*H-J*I0;B=J*I1-H*C1;C=J*I1-H*C2;D=C1*C2-J*I2
    Del=A*D-B*C
    E=A*x+C;Y=-(B*x+D);II=E*(I2-x*I1)+Y*(x*I0-I1)
    al=E*C1-Y*H;be=C2-x*H
    P5=(X-a)*(X-h)*(X-d)*(X-x)*(E*X-Y)
    mo=[integ(X*(1-X)*P5,j) for j in range(4)]
    EL=lambda q:[q**(i+1) for i in range(5)]
    ER=lambda q:[(1-q)*q**i for i in range(5)]
    dl0=[T.one]+[T.zero]*4;dl1=[(i+1)*a**i for i in range(5)]
    dr0=[T.one]*5;dr1=[d**i-(b*i*d**(i-1) if i else 0) for i in range(5)]
    Dx=[a**5*q-30*at(P,x)*r for q,r in zip(EL(x),EL(a))]
    Fx=[b**5*q-30*at(Q,x)*r for q,r in zip(ER(x),ER(d))]
    K0,K1=[dot(Dx,r).exquo(a*x*(a-x)) for r in [dr0,dr1]]
    KL0,KL1=[dot(l,Fx).exquo(b*(1-x)*(x-d)) for l in [dl0,dl1]]
    Ta,Tb=ev(T4,a),ev(T4,b)
    Uab=ev([ev(row,b) for row in U4],a)
    return locals()

def build(mode):
    B=common_model(QQ)
    ctx=flint.fmpq_mpoly_ctx.get(('a','z'))
    a,z=ctx.gens()
    frac=lambda c:flint.fmpq(int(c.numerator),int(c.denominator))
    cv=lambda p:ctx.from_dict({(j,i):frac(c) for (i,),u in p.items() for (j,),c in u.items()})
    ca=lambda u:ctx.from_dict({(m,0):frac(c) for (m,),c in u.items()})
    bh=lambda p,q:sum(c*q**(i) for i,c in enumerate(p))
    coeff=lambda q:[ca(q.get((j,),B['ar'].zero)) for j in range(q.degree()+1)]
    hom=lambda p,n,d:sum(c*n**i*d**(len(p)-1-i) for i,c in enumerate(p))
    ev=lambda p,u:sum(cv(c)*u**j[0] for j,c in p.items())
    H,C1,C2,J,I0,I1,I2,E,Y,Del,Ta,Tb,Uab=[cv(B[k]) for k in
        ('H','C1','C2','J','I0','I1','I2','E','Y','Del','Ta','Tb','Uab')]
    b=2-a;d=a-1;h=a/2
    ff4=33*a**4-132*a**3+176*a*a-88*a+16
    ff6=2475*a**6-14850*a**5+34140*a**4-37560*a**3+20136*a*a-4752*a+352
    assert 1646877554784000000*Del==-a*a*(a-2)**2*ff4*ff6
    K0,K1,M0,M1=map(lambda k:coeff(B[k]),('K0','K1','KL0','KL1'))
    assert all(len(c)==4 for c in [K0,K1,M0,M1])
    # Work with homogeneous coordinates and cancel only their common
    # exact factors; an actual denominator has already been earned.
    cancellations={}
    def shrink(n,d,name):
        g=n.gcd(d)
        cancellations[name]=g.degrees() if not g.is_constant() else (0,0)
        return n//g,d//g
    Y,E=shrink(Y,E,'moebius')
    k0,k1=bh(K0,z),bh(K1,z)
    k1,k0=shrink(k1,k0,'right-line')
    g0=k1-Tb*k0;g1=Ta*k1-Uab*k0
    g1,g0=shrink(g1,g0,'left-line')
    if mode=='right-matched':
        td=(Y-d*E)*k0+(E-Y)*k1;tn=d*(Y-d*E)*k0+(E-Y)*k1
        tn,td=shrink(tn,td,'shared')
        xd=(a*td-tn)*g0+tn*g1;xn=a*(a*td-tn)*g0
    elif mode=='right-opposite':
        td=(a*E-Y)*g0+Y*g1;tn=a*(a*E-Y)*g0
        tn,td=shrink(tn,td,'shared')
        xd=(tn-d*td)*k0+(td-tn)*k1;xn=d*(tn-d*td)*k0+(td-tn)*k1
    else: raise AssertionError(mode)
    xn,xd=shrink(xn,xd,'middle')
    er0,er1=[cv(dot(B["EL"](B["a"]),v)) for v in [B["dr0"],B["dr1"]]]
    ph_a=er0*k1-er1*k0
    b0,b1=[cv(dot(v,B['ER'](B['d']))) for v in [B['dl0'],B['dl1']]]
    ph_d=b0*g1-b1*g0
    qdet=lambda n,e:sum((K0[i]*k1-K1[i]*k0)*sum(n**(i-1-j)*e**(2-(i-1-j))*z**j for j in range(i)) for i in range(1,4))
    rt2=lambda n,dd:g1*hom(M0,n,dd)-g0*hom(M1,n,dd)
    if mode=='right-matched':
        G1=rt2(Y,E)
        G2=a*(C2-z*H)*qdet(xn,xd)+30*xn*(a*xd-xn)*J*ph_a
    else:
        G1=a*(xd*(I2-z*I1)+xn*(z*I0-I1))*qdet(Y,E)+30*Y*(a*E-Y)*(C1*xd-xn*H)*ph_a
        G2=b*(C1*E-Y*H)*rt2(xn,xd)+30*(xd-xn)*(xn-d*xd)*(E*xn-Y*xd)*J*ph_d
    co=[ctx.constant(1)]
    for n,den in [(a,1),(d,1),(h,1),(Y,E),(tn,td),(xn,xd)]:
        co=[den*a1-n*b1 for a1,b1 in zip([ctx.constant(0)]+co,co+[ctx.constant(0)])]
    mw0=sum(c/flint.fmpq((i+2)*(i+3)) for i,c in enumerate(co))
    mw1=sum(c/flint.fmpq((i+3)*(i+4)) for i,c in enumerate(co))
    mw2=sum(c/flint.fmpq((i+4)*(i+5)) for i,c in enumerate(co))
    S0=mw1-z*mw0; S1=mw2-z*mw1
    I=E*xd*I2-(E*xn+Y*xd)*I1+Y*xn*I0
    Ssup=I*(z-h)*(z*td-tn)+mw0*z*(z-1)*(z-a)*(z-d)
    Sd=b*I*rt2(z,1)+30*(C2*xd-xn*H)*(E*z-Y)*(1-z)*(z-d)*ph_d
    VD=(1-z)*(z-d);VL=z*(z-a)
    Dx=[cv(q) for q in B['Dx']]
    Fx=[cv(q) for q in B['Fx']]
    Rs=[cv(q) for q in B['ER'](B['d'])]
    Dd=(210*dot(Dx,[I*qq+30*(C2*xd-xn*H)*(E*z-Y)*VD**2*rp for qq,rp in zip(Fx,Rs)]))
    Dd-=a**5*b**5*(z*xd-xn)*(z*E-Y)*VD**2*VL**2
    assert not Dd%(VD*VL);Dd=Dd//(VD*VL)
    guards=[a,b,a-1,z,z-1,z-a,z-d,z-h,E,td,xd,Del,k0,k1,g0,g1]
    guards.extend([n-den*w for n,den in [(Y,E),(tn,td),(xn,xd)] for w in (0,1,a,h,d,z)])
    guards.extend([Y*td-tn*E,Y*xd-xn*E,tn*xd-xn*td,I,mw0])
    raw=[('G1',G1),('G2',G2),('S0',S0),('S1',S1),('Sup',Ssup),('Port',Sd),('Diag',Dd)]
    def trim(f):
        out=[]
        for j,g in enumerate(guards):
            while f:
                h1=f.gcd(g)
                if h1.is_constant():break
                f=f//h1;out.append((j,h1.degrees()))
        return f,out
    result=[(k,*trim(f)) for k,f in raw]
    return locals()


from math import gcd,lcm,factorial
from functools import reduce
from time import monotonic
import sympy as s
import flint

def irep(f):
    q=f.to_dict()
    L=lcm(*(int(c.denominator) for c in q.values()))
    B={k:int(v.numerator)*(L//int(v.denominator)) for k,v in q.items()}
    g=gcd(*B.values())
    return {k:v//g for k,v in B.items()}

def l1(f):return sum(abs(n) for n in f.values())
def da(f):return max(i[0] for i in f)
def dz(f):return max(i[1] for i in f)

def exact(prim,rest):
    bounds={k:factorial(dz(prim)+dz(f))*l1(prim)**dz(f)*l1(f)**dz(prim) for k,f in rest.items()}
    degree={k:da(prim)*dz(f)+da(f)*dz(prim) for k,f in rest.items()}
    print('integer coefficient bounds bits',[b.bit_length() for b in bounds.values()],flush=True)
    buf={k:[0]*(n+1) for k,n in degree.items()}
    p=2**61-1; M=1; count=0
    t=monotonic()
    while M<=2*max(bounds.values()):
        p=int(s.nextprime(p));assert flint.fmpz(p).is_prime()
        D=flint.nmod_mpoly_ctx.get(('z','a'),p)
        lift=lambda T:D.from_dict({(j,i):v%p for (i,j),v in T.items()})
        A=lift(prim)
        rhs={k:lift(f) for k,f in rest.items()}
        if A.degrees()[0]!=dz(prim) or any(rhs[k].degrees()[0]!=dz(rest[k]) for k in rhs):continue
        mp=pow(M%p,-1,p)
        for k,T in rhs.items():
            R=A.resultant(T,'z')
            assert all(not i and j<=degree[k] for i,j in R.to_dict())
            rs={j:int(v) for (i,j),v in R.to_dict().items()}
            for j,cur in enumerate(buf[k]):
                buf[k][j]+=M*((rs.get(j,0)-cur)*mp%p)
        M*=p;count+=1
        if count%20==0:print('  CRT progress',count,round(monotonic()-t,2),flush=True)
    ans={}
    for k,b in buf.items():
        v=[a-M if 2*a>M else a for a in b]
        assert all(abs(a)<=bounds[k] for a in v)
        ans[k]=flint.fmpz_poly(v)
    print('projection degrees',[(k,v.degree()) for k,v in ans.items()], 'primes',count,flush=True)
    return ans


def local_elimination(mode,width):
    B=build(mode)
    A=flint.fmpq_poly([0,1])
    delta=A**2*(A-2)**2*(33*A**4-132*A**3+176*A**2-88*A+16)*(2475*A**6-14850*A**5+34140*A**4-37560*A**3+20136*A**2-4752*A+352)
    d0=B['d']
    guards0=B['guards']
    fselect={k:f for k,f,_ in B['result']}
    tests=[fselect[k] for k in ('G1','S0','S1','Port')]
    seen=set()
    table={'right-matched':{17:(12,17,1),27:(13,20,1),21:(12,13,1)},
           'right-opposite':{51:(13,26,1),32:(12,23,1),6:(3,3,1),9:(5,5,1),14:(14,16,1),18:(15,18,1),21:(12,13,3)}}[mode]

    for F,n in width:
        F=flint.fmpq_poly(F);F=F/F[F.degree()]
        if not delta%F:continue
        deg=F.degree()
        assert deg not in seen
        seen.add(deg)
        i,j,pow1=table[deg]
        print('exact coefficient width',deg,'guard pair',i,j,'removed power',pow1,flush=True)
        ZZ=flint.fmpq_poly()
        O=flint.fmpq_poly([1])
        def to_coeffs(g):
            n=g.degrees()[1]
            u=[{} for _ in range(n+1)]
            for (i,j),c in g.to_dict().items():u[j][i]=c
            return [flint.fmpq_poly([mp.get(i,0) for i in range(max(mp,default=0)+1)])%F for mp in u]
        def trim(r):
            q=r[:]
            while q and not q[-1]:q.pop()
            return q
        def inv(r):
            d,s,t=r.xgcd(F)
            assert d==O
            return s
        def rem(p,q):
            p,q=trim(p),trim(q)
            if not q:raise ZeroDivisionError()
            z=inv(q[-1])
            while len(p)>=len(q):
                rat=(p[-1]*z)%F
                d=len(p)-len(q)
                for i,w in enumerate(q):
                    p[i+d]=(p[i+d]-rat*w)%F
                p=trim(p)
            return p
        def gcd(p,q):
            p,q=trim(p),trim(q)
            while q:p,q=q,rem(p,q)
            c=inv(p[-1])
            return [(a*c)%F for a in p]
        def taylor(p,root,degree):
            coeff=[ZZ]*degree
            for c in reversed(to_coeffs(p)):
                for j in range(degree-1,0,-1):
                    coeff[j]=(coeff[j]*root+coeff[j-1])%F
                coeff[0]=(coeff[0]*root+c)%F
            return coeff
        uu=gcd(to_coeffs(guards0[i]),to_coeffs(guards0[j]))
        assert len(uu)==2 and uu[1]==O
        xg=-uu[0]
        assert not taylor(guards0[i],xg,1)[0]
        assert all(not any(taylor(test,xg,pow1)) for test in tests)
        print('  exact live guard root and division verified',flush=True)
        # Leading quotient of a monic division equals leading input.
        exact_degs=[len(trim(to_coeffs(q)))-1-pow1 for q in tests]
        for p in [101,103,107,109,113,127,131,137,139,149,151,157,163,167]:
            possible=set(range(len(tests)))
            try:
                NZ=flint.fmpz_mod_poly_ctx(p)
                red=lambda q:int(q.numerator)%p*pow(int(q.denominator),-1,p)%p
                fp=NZ([red(q) for q in F.coeffs()])
                assert fp.degree()==deg
                qroot=NZ([red(q) for q in xg.coeffs()])
                details=[]
                for f,k in fp.factor()[1]:
                    assert k==1
                    K=flint.fq_default_ctx(modulus=f,fq_type='FQ_NMOD')
                    R=flint.fq_default_poly_ctx(K)
                    a=K.gen()
                    fromQ=lambda q:sum((K(red(c))*a**j for j,c in enumerate(q.coeffs())),K.zero())
                    g0=R([-fromQ(xg),K.one()])**pow1
                    vals=[]
                    for t in tests:
                        v=[K.zero()]*(t.degrees()[1]+1)
                        for (i,j),c in t.to_dict().items():v[j]+=K(red(c))*a**i
                        u=R(v)
                        assert not u % g0
                        vals.append(u//g0)
                    possible&={j for j,q in enumerate(vals) if q.degree()==exact_degs[j]}
                    gg=reduce(lambda p,q:p.gcd(q),vals)
                    assert gg.degree()==0
                    details.append(f.degree())
                assert possible
            except (AssertionError,ValueError,ZeroDivisionError):
                continue
            print('  unit ideal mod',p,'component degrees',details,'uniform leading rows',sorted(possible),flush=True)
            break
        else:
            raise AssertionError(("no unit-lift prime",mode,deg))
    assert seen==set(table)


AA=s.Symbol('a')
F4=33*AA**4-132*AA**3+176*AA**2-88*AA+16
F6=2475*AA**6-14850*AA**5+34140*AA**4-37560*AA**3+20136*AA**2-4752*AA+352

def chart(fix,which,orientation):
    F=F4 if which==4 else F6
    assert s.Poly(F,AA).is_irreducible
    K=QQ.algebraic_field(s.CRootOf(F,0))
    R,s0=ring('s',K);a=R(K.unit);b=2-a;h=a/2;d=a-1
    W,X=ring('X',R)
    V=X**2*(X-a)**2;Vr=(1-X)**2*(X-d)**2
    anti=lambda f:sum(c*X**(i[0]+1)/(i[0]+1) for i,c in f.items())
    P=anti(V);Q0=anti(Vr);Q=W(sum(Q0.values()))-Q0
    H=integ(P*Vr);C1=integ(P*Vr,1);C2=integ(V*Q,1);J=integ(P*Q)
    I0,I1,I2=[integ(V*Vr,j) for j in range(3)]
    A=H*H-J*I0;Br=J*I1-H*C1;Cr=J*I1-H*C2;D=C1*C2-J*I2
    assert A and A*D==Br*Cr
    if fix=='z':z=-Cr.exquo(A);y=s0
    else:y=-Br.exquo(A);z=s0
    el=lambda u:[u**(i+1) for i in range(5)]
    er=lambda u:[(1-u)*u**i for i in range(5)]
    dl0=[R.one]+[R.zero]*4;dl1=[(i+1)*a**i for i in range(5)]
    dr0=[R.one]*5;dr1=[d**i-(b*i*d**(i-1) if i else 0) for i in range(5)]
    DX=[a**5*u-30*P*v for u,v in zip(el(X),el(a))]
    FX=[b**5*u-30*Q*v for u,v in zip(er(X),er(d))]
    K0p,K1p=[dot(DX,v).exquo(W(a)*X*(W(a)-X)) for v in [dr0,dr1]]
    M0p,M1p=[dot(u,FX).exquo(W(b)*(1-X)*(X-W(d))) for u in [dl0,dl1]]
    k0,k1=at(K0p,z),at(K1p,z)
    Ta,Tb=ev(T4,a),ev(T4,b)
    Uab=ev([ev(row,b) for row in U4],a)
    g0=k1-Tb*k0;g1=Ta*k1-Uab*k0
    if which==6 and fix=='z':
        assert not g0 and not g1
        print('F6 fixed z: exact left port dropout',orientation,flush=True)
        return
    assert all([k0,k1,g0,g1])
    if orientation==0:
        td=(y-d)*k0+(1-y)*k1;tn=d*(y-d)*k0+(1-y)*k1
        xd=(a*td-tn)*g0+tn*g1;xn=a*(a*td-tn)*g0
    else:
        td=(a-y)*g0+y*g1;tn=a*(a-y)*g0
        xd=(tn-d*td)*k0+(td-tn)*k1;xn=d*(tn-d*td)*k0+(td-tn)*k1
    assert td and xd
    p=(X-a)*(X-d)*(X-h)*(X-y)*(td*X-tn)*(xd*X-xn)
    wt=X*(1-X)*p
    s1,s2=[integ((X-z)*wt,j) for j in range(2)]
    g=s1.gcd(s2).monic()
    print('width',which,'fixed',fix,'orientation',orientation,'shift degs',s1.degree(),s2.degree(),'gcd',g.degree(),flush=True)
    if which==4:
        assert (s1.degree(),s2.degree())==((10,10) if fix=="y" else (3,3))
        assert g.degree()==0
    else:
        assert fix=="y" and (s1.degree(),s2.degree())==(10,10)
        assert g.degree()==(3 if orientation==0 else 6)
        factor=g0.exquo(z*(z-a))
        assert factor.degree()==1
        assert g==(z*(z-a)*factor.monic())**(orientation+1)
    print("  excluded exactly",flush=True)


def verify_regular(mode):
    B=build(mode)
    names=("G1","S0","S1","Port")
    arr={k:f for k,f,s in B["result"]}
    exact_proj=exact(irep(arr["G1"]),{k:irep(arr[k]) for k in names[1:]})
    degrees=[r.degree() for r in exact_proj.values()]
    monic_gcd=reduce(lambda f,g:f.gcd(g),exact_proj.values())
    factors=monic_gcd.factor()[1]
    if mode=="right-matched":
        assert degrees==[624,624,616] and monic_gcd.degree()==279
        assert sorted((f.degree(),n) for f,n in factors)==[(1,2),(1,92),(4,6),(6,9),(17,1),(21,3),(27,1)]
    else:
        assert degrees==[1253,1257,1193] and monic_gcd.degree()==668
        assert sorted((f.degree(),n) for f,n in factors)==[(1,8),(1,156),(4,6),(6,2),(6,19),(9,2),(14,2),(18,2),(21,9),(32,1),(51,1)]
    print(mode,"exact projected gcd",monic_gcd.degree(),flush=True)
    local_elimination(mode,factors)

if __name__=="__main__":
    for degree in [4,6]:
        for fix in ["y","z"]:
            for orientation in [0,1]:
                chart(fix,degree,orientation)
    for mode in ["right-matched","right-opposite"]:
        verify_regular(mode)

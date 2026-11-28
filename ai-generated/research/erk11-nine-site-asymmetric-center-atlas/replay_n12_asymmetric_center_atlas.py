"""Asymmetric central atlas: exact matched and affine-zero exits, finite opposite regular atlas.
Requires SymPy and python-flint 0.9 or compatible. All coefficient operations are exact.
"""
from math import comb
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
    z0,z1=[at(f,e) for f in Ms]
    lS=-a*z0; lP=z0-z1; lc=a*a*z0
    rS=-d*k0+k1;rP=k0-k1;rc=d*d*k0-k1
    delta=rS*lP-rP*lS
    sN=rP*lc-rc*lP;pN=lS*rc-rS*lc
    L0=a*a*delta-a*sN+pN; L1=-pN
    R0=d*d*delta-d*sN+pN;R1=-delta+sN-pN
    F=L0*R0+ev(T4,a)*L1*R0+ev(T4,b)*L0*R1+ev([ev(row,b) for row in U4],a)*L1*R1
    H6=(X-a)*(X-h)*(X-d)*(X-e)*(delta*X*X-sN*X+pN)
    m=[integ(X*(1-X)*H6,j) for j in range(3)]
    g=m[0]*m[2]-m[1]*m[1]
    v,w=m[0],m[1]
    Sup=I*(delta*w*w-sN*w*v+pN*v*v)*v+w*(w-v)*(w-a*v)*(w-d*v)
    known=[a,b,a-1,a-2,b-1,b-2,a+b-1,a+b-2,2*a+b-2,a+2*b-2,I]
    live=known+[delta,v,w,w-v,w-a*v,w-d*v,w-h*v,w-e*v,
                L0,L1,R0,R1,sN*sN-4*delta*pN]
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
        D=flint.nmod_mpoly_ctx.get(('b','a'),p)
        lift=lambda T:D.from_dict({(j,i):v%p for (i,j),v in T.items()})
        A=lift(prim)
        rhs={k:lift(f) for k,f in rest.items()}
        if A.degrees()[0]!=dz(prim) or any(rhs[k].degrees()[0]!=dz(rest[k]) for k in rhs):continue
        mp=pow(M%p,-1,p)
        for k,T in rhs.items():
            R=A.resultant(T,'b')
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


def verify_matched_fibers(mode,widths):
    Fs,guards,_,_=data(mode)
    tests=[Fs[k] for k in ('K','RLR','RLG','QR')]
    ar,a=ring('a',QQ);br,b=ring('b',ar)
    def into(f):
        p={}
        for (i,j),c in f.to_dict().items():
            p.setdefault((int(j),),{})[(int(i),)]=QQ(int(c.numerator))/int(c.denominator)
        return br.from_dict({j:ar.from_dict(v) for j,v in p.items()})
    ac=lambda c:flint.fmpq(int(c.numerator),int(c.denominator))
    def ac0(u):
        if not u:return flint.fmpq_poly()
        return flint.fmpq_poly([ac(u.get((i,),QQ.zero)) for i in range(u.degree()+1)])
    def to_coeffs(f):
        s=into(f)
        return [ac0(s.get((i,),ar.zero)) for i in range(s.degree()+1)]
    A=flint.fmpq_poly([0,1]);delta=A*(A-1)*(A-2)
    table={(3,2):(None,None,0),(3,8):(1,1,2),(6,12):(10,11,3),(9,16):(10,11,4)}
    seen=set()
    for f,n0 in widths:
        F=flint.fmpq_poly(f);F=F/F[F.degree()]
        key=(F.degree(),n0)
        deg=F.degree();i,j,n=table[key];seen.add(key)
        if i in (None,1):
            L,Q=flint.fmpq_poly([1]),flint.fmpq_poly([])
        else:
            g0=guards[i].gcd(guards[j])
            sr=into(guards[i]//g0).subresultants(into(guards[j]//g0))
            lin=[q for q in sr if q.degree()==1][-1]
            L=ac0(lin[(1,)])%F;Q=ac0(lin[(0,)])%F
        assert L
        def true_degree(f):
            p=[c%F for c in to_coeffs(f)]
            while p and not p[-1]:p.pop()
            assert p
            return p
        testpol=[true_degree(f) for f in tests]
        gds=[true_degree(guards[k]) for k in (i,j) if k is not None]
        print('width',deg,'exact homogeneous guard',i,j,'power',n,flush=True)
        # Multiply each Taylor coefficient at -Q/L by L^(degree-r).
        cap=max(len(q) for q in gds+testpol)
        lp=[flint.fmpq_poly([1])];qp=lp[:]
        for _ in range(cap):
            lp.append((lp[-1]*L)%F)
            qp.append((-qp[-1]*Q)%F)
        def exact_at(cs,r):
            d=len(cs)-1
            return sum((comb(z,r)*cs[z]*qp[z-r]*lp[d-z])%F for z in range(r,d+1))%F
        assert not any(exact_at(f,0) for f in gds)
        assert not any(exact_at(f,r) for f in testpol for r in range(n))
        for prime in [101,103,107,109,113,127,131,137,139,149,151]:
            try:
                Nz=flint.fmpz_mod_poly_ctx(prime)
                red=lambda c:int(c.numerator)%prime*pow(int(c.denominator),-1,prime)%prime
                redP=lambda p:Nz([red(c) for c in p.coeffs()])
                Fp=redP(F)
                assert Fp.degree()==deg and redP(L).gcd(Fp).degree()==0
                js=set(range(len(tests)))
                ds=[]
                for q,k in Fp.factor()[1]:
                    assert k==1
                    K=flint.fq_default_ctx(modulus=q,fq_type='FQ_NMOD')
                    R=flint.fq_default_poly_ctx(K);a=K.gen()
                    v=lambda p:sum((K(red(c))*a**i for i,c in enumerate(p.coeffs())),K.zero())
                    common=R([v(Q)/v(L),K.one()])**n
                    ts=[]
                    for dc in testpol:
                        t=R([v(c) for c in dc])
                        assert not t%common
                        ts.append(t//common)
                    js&={i for i,t in enumerate(ts) if t.degree()==len(testpol[i])-1-n}
                    assert reduce(lambda a,b:a.gcd(b),ts).degree()==0
                    ds.append(q.degree())
                assert js
            except (AssertionError,ValueError,ZeroDivisionError):continue
            print('  whole lift',prime,'component degrees',ds,'full degree rows',sorted(js),flush=True)
            break
        else:raise AssertionError(("no prime checked",deg))
    assert seen==set(table)




def verify_affine_zero(mode):
    R,G,A,C=build(mode,raw_s=True)
    widths=flint.fmpq_mpoly_ctx.get(('b','a'))
    frac=lambda q:flint.fmpq(int(q.numerator),int(q.denominator))
    lift=lambda w:widths.from_dict({(j,i):frac(c) for (i,j,k),c in w.items() if k==0})
    assert all(k==0 for w in [A,C] for i,j,k in w)
    known=[lift(g) for g in G[:10]]
    def trim(w):
        f=lift(w)
        for p in known:
            while not f%p:f=f//p
        return f
    a0=s.Symbol('a')
    U,V=map(trim,(A,C))
    v=U.resultant(V,'b')
    assert v.degrees()==(0,24 if mode=="matched" else 32)
    fs=v.factor()[1]
    assert sorted((p.degrees()[1],n) for p,n in fs)==(
        [(3,1),(3,2),(6,1),(9,1)] if mode=="matched"
        else [(1,3),(1,8),(6,1),(15,1)])
    def wp(p):
        q=0
        for (j,i),c in p.to_dict().items():
            assert not j
            q+=s.Rational(int(c.numerator),int(c.denominator))*a0**int(i)
        return s.Poly(q,a0,domain=QQ)
    for pf,_ in fs:
        a=wp(pf)
        if not (s.Poly(a0*(a0-1)*(a0-2),a0)).rem(a):continue
        K=QQ.algebraic_field(s.CRootOf(a,0));aa=K.unit
        B,b=ring('b',K)
        def into(f):
            return sum(B(K.convert(s.Rational(int(c.numerator),int(c.denominator))))*aa**int(i)*b**int(j)
                       for (j,i),c in f.to_dict().items())
        u=into(U).gcd(into(V)).monic()
        print(mode,'a deg',a.degree(),'b gcd deg',u.degree(),flush=True)
        for pp,n in u.factor_list()[1]:
            assert pp.degree()==1
            bb=-pp.get((0,),K.zero)/pp.LC
            def into(f):
                cen=0
                for (i,j,k),c in f.items():cen+=B(K.convert(c)*aa**i*bb**j)*b**k
                return B(cen)
            # check nonzero width guards as facets.
            if any(not into(w) for w in G[:10]):
                print('entire width violates a calibration or endpoint guard',flush=True);continue
            ps=[into(z) for z in R.values()]
            gg=reduce(lambda f,h:f.gcd(h),ps)
            print('  raw s gcd',gg.degree(),flush=True)
            for i,w in enumerate(map(into,G)):
                if not w:
                    print("  full scalar fiber violates a live guard",i,flush=True)
                    break
                while gg.degree()>0:
                    p=gg.gcd(w)
                    if not p.degree():break
                    gg=gg.exquo(p)
                    print('    trim live guard',i,p.degree(),flush=True)
            else:
                print('  after exact guard checks',gg.degree(),flush=True)
                assert gg.degree()==0


def verify_width_factor():
    R,a,b=ring("a,b",QQ);h=model(R,a,b)
    A,B,C,D,J=[h[k] for k in ("A","B","C","D","J")]
    Tb=ev(T4,b)
    E=ev([ev(row,b) for row in U4],a)-ev(T4,a)*Tb
    assert 633719116800000*(A*D-B*C)==-a*b*J*E
    deriv=E.exquo(a*b)
    K0,K1=h["Ks"]
    atforced=lambda f:sum(c*(-C)**i[0]*A**(3-i[0]) for i,c in f.items())
    ctx=flint.fmpq_mpoly_ctx.get(("a","b"))
    cv=lambda f:ctx.from_dict({ij:flint.fmpq(int(v.numerator),int(v.denominator)) for ij,v in f.items()})
    assert not cv(atforced(K1)-Tb*atforced(K0))%cv(deriv)
    ds=[cv(A).resultant(cv(C),"b"),cv(deriv).resultant(cv(A),"b"),cv(deriv).resultant(cv(C),"b")]
    g=reduce(lambda p,q:p.gcd(q),ds)
    assert g.degrees()==(12,0)
    print("general width determinant and homogeneous derivative alignment verified",flush=True)

def verify_matched():
    B,_,_,_=data("matched")
    C={k:irep(f) for k,f in B.items()}
    rr=exact(C["K"],{k:C[k] for k in ("RLR","RLG","QR")})
    assert [f.degree() for f in rr.values()]==[508,846,668]
    g=reduce(lambda p,q:p.gcd(q),rr.values())
    assert g.degree()==246
    fs=g.factor()[1]
    assert sorted((f.degree(),n) for f,n in fs)==[(3,2),(3,8),(6,12),(9,16)]
    verify_matched_fibers("matched",fs)

def verify_finite_opposite():
    P,_,_,_=data("opposite")
    assert P["QG"].degrees()==(44,40) and P["RLR"].degrees()==(50,45)
    assert P["QG"].gcd(P["RLR"]).is_constant()
    print("regular opposite center exact constant bivariate gcd; finite atlas",flush=True)

if __name__=="__main__":
    verify_width_factor()
    verify_affine_zero("matched")
    verify_affine_zero("opposite")
    verify_matched()
    verify_finite_opposite()

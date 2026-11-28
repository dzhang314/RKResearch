"""Complete characteristic-zero four-distinct same-free-pair clock exit.
Requires SymPy and python-flint 0.9 or compatible. All projections,
fiber reductions and leading units are exact; no numeric scouting.
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

def matched_center_shapes(branch):
    R,a,b=ring('a,b',QQ);B=model(R,a,b)
    C=flint.fmpq_mpoly_ctx.get(('a','b'))
    cv=lambda q:C.from_dict({k:flint.fmpq(int(c.numerator),int(c.denominator)) for k,c in q.items()})
    gu=[cv(u) for u in B['live' if branch=='regular' else 'known']]
    qs={}
    names=('Cmat','F','g','Sup') if branch=='regular' else ('Cmat','delta','sN','pN')
    for k in names:
        f=cv(B[k]);st=[]
        for j,w in enumerate(gu):
            while True:
                q=f.gcd(w)
                if q.is_constant():break
                st.append((j,q.degrees()));f=f//q
        qs[k]=f
        print(branch,k,f.degrees(),st,flush=True)
    return B,C,qs,gu


def build_opposite_center():
    R,a,b,z=ring('a,b,z',QQ);B=model(R,a,b)
    X=B['X'];d,h,e=[B[k] for k in ('d','h','e')]
    I,I0,I1,I2,H,C1,C2=[B[k] for k in ('I','I0','I1','I2','H','C1','C2')]
    P4=(X-a)*(X-d)*(X-h)*(X-e)
    m=[integ(X*(1-X)*P4,j) for j in range(5)]
    f=[m[j+1]-z*m[j] for j in range(4)]
    D=f[0]*f[2]-f[1]*f[1]
    SN=f[0]*f[3]-f[1]*f[2];PN=f[1]*f[3]-f[2]*f[2]
    L0=a*a*D-a*SN+PN;L1=-PN
    R0=d*d*D-d*SN+PN;R1=-D+SN-PN
    l=[L0*u+L1*v for u,v in zip(B['dl0'],B['dl1'])]
    r=[R0*u+R1*v for u,v in zip(B['dr0'],B['dr1'])]
    aa=B['el'](a);dd=B['er'](d)
    P,Q=B['P'],B['Q']
    at=lambda f,v:sum(c*v**j[0] for j,c in f.items())
    vL=z*(z-a);vR=(1-z)*(z-d)
    lf=[I*(a**5*p-30*at(P,z)*q)+30*(C1-h*H)*(z-e)*vL*vL*q for p,q in zip(B['el'](z),aa)]
    rf=[I*(b**5*p-30*at(Q,z)*q)+30*(C2-e*H)*(z-h)*vR*vR*q for p,q in zip(B['er'](z),dd)]
    l3=[v.exquo(vL) for v in lf]
    r3=[v.exquo(vR) for v in rf]
    C=B['Copp']
    F=dot(l,r)
    ML=a*(I2-(e+z)*I1+e*z*I0)*(B['k0']*R0+B['k1']*R1)+30*h*(a-h)*(h-e)*(C1-z*H)*dot(aa,r)
    MR=b*(I2-(h+z)*I1+h*z*I0)*(B['z0']*L0+B['z1']*L1)+30*(1-e)*(e-d)*(e-h)*(C2-z*H)*dot(l,dd)
    Diag=210*dot(l3,r3)-a**5*b**5*I*(z-h)*(z-e)*vL*vR
    Pu=dot(l3,r);Pv=dot(l,r3)
    Su=I*(D*z*z-SN*z+PN)+(D*m[2]-SN*m[1]+PN*m[0])*z*(z-1)*(z-a)*(z-d)
    guard=B['known']+[z,z-1,z-a,z-h,z-d,z-e,D,*[D*t*t-SN*t+PN for t in (0,1,a,d,h,e,z)],SN*SN-4*D*PN]
    raw={'C':C,'F':F,'ML':ML,'MR':MR,'B':Diag}
    return raw,guard

def opposite_center_data(mod=None):
    raw,gu=build_opposite_center()
    C=(flint.fmpq_mpoly_ctx.get(('z','b','a')) if mod is None else flint.nmod_mpoly_ctx.get(('z','b','a'),mod))
    def cv(q):
        if mod is None: return flint.fmpq(int(q.numerator),int(q.denominator))
        return int(q.numerator)%mod*pow(int(q.denominator),-1,mod)%mod
    ff=lambda f:C.from_dict({(k[2],k[1],k[0]):cv(c) for k,c in f.items()})
    gs=[ff(f) for f in gu]
    d={}
    for k,f in raw.items():
        x=ff(f);rs=[]
        for i,g in enumerate(gs):
            while not x%g:x=x//g;rs.append(i)
        d[k]=x;print(k,x.degrees(),rs,flush=True)
    return d,gs

def opposite_center_projections(names,mod=None):
    q,gs=opposite_center_data(mod)
    C=(flint.fmpq_mpoly_ctx.get(('b','a')) if mod is None else flint.nmod_mpoly_ctx.get(('b','a'),mod))
    tr=lambda f:C.from_dict({(k[1],k[2]):c for k,c in f.to_dict().items()})
    p=tr(q['C'])
    l=names[0]
    rs=[]
    for k in names[1:]:
        r=q[l].resultant(q[k],'z');assert r.degrees()[0]==0
        print('z elimination',l,k,r.degrees(),flush=True)
        f=p.resultant(tr(r),'b')
        rs.append((k,f))
        print('width projection',k,f.degrees(),flush=True)
        if len(rs)>1:
            g=reduce(lambda u,v:u.gcd(v),[v for k,v in rs])
            print('gcd',g.degrees(),[(w.degrees()[1],n) for w,n in g.factor()[1]],flush=True)
    return rs


def build_edge(mode):
    R,a,b,z=ring('a,b,z',QQ);B=model(R,a,b)
    X=B['X'];d,h,e=[B[k] for k in ('d','h','e')]
    x,y=(h,e) if mode=='matched' else (e,h)
    I,I0,I1,I2,H,C1,C2,J,A,B0,C0,D0=[B[k] for k in ('I','I0','I1','I2','H','C1','C2','J','A','B','C','D')]
    ZD=A*y+B0; ZN=-(C0*y+D0)
    P4=(X-a)*(X-d)*(X-h)*(X-e)
    m=[integ(X*(1-X)*P4,j) for j in range(5)]
    f=[m[j+1]-z*m[j] for j in range(4)]
    D=f[0]*f[2]-f[1]*f[1]
    SN=f[0]*f[3]-f[1]*f[2];PN=f[1]*f[3]-f[2]*f[2]
    L0=a*a*D-a*SN+PN;L1=-PN
    R0=d*d*D-d*SN+PN;R1=-D+SN-PN
    l=[L0*u+L1*v for u,v in zip(B['dl0'],B['dl1'])]
    r=[R0*u+R1*v for u,v in zip(B['dr0'],B['dr1'])]
    aa=B['el'](a);dd=B['er'](d)
    at=lambda f,v:sum(c*v**j[0] for j,c in f.items())
    vL=z*(z-a);vR=(1-z)*(z-d)
    K0z,K1z=[at(f,z) for f in B['Ks']]
    M0z,M1z=[at(f,z) for f in B['Ms']]
    F=dot(l,r)
    G=K0z*R0+K1z*R1
    Le=B['z0']*L0+B['z1']*L1
    Paar=dot(l,dd)
    Port=b*I*(L0*M0z+L1*M1z)+30*(C2-x*H)*(z-y)*vR*Paar
    if mode=='matched':
        Rmark=Le
        Lmark=a*(C2-z*H)*(R0*B['k0']+R1*B['k1'])+30*h*(a-h)*(h-z)*J*dot(aa,r)
    else:
        Rmark=b*(C1-h*H)*Le+30*(1-e)*(e-d)*(e-h)*J*Paar
        Lmark=a*(I2-(e+z)*I1+e*z*I0)*(R0*B['k0']+R1*B['k1'])+30*h*(a-h)*(h-z)*(C1-e*H)*dot(aa,r)
    Su=I*(D*z*z-SN*z+PN)+(D*m[2]-SN*m[1]+PN*m[0])*z*(z-1)*(z-a)*(z-d)
    guard=B['known']+[z,z-1,z-a,z-h,z-d,z-e,D,*[D*t*t-SN*t+PN for t in (0,1,a,d,h,e,z)],SN*SN-4*D*PN]
    raw={'F':F,'G':G,'R':Rmark}
    return raw,guard,ZD,ZN

def edge_data(mode):
    raw,gu,ZD,ZN=build_edge(mode)
    C=flint.fmpq_mpoly_ctx.get(('z','b','a'))
    rd=lambda q:flint.fmpq(int(q.numerator),int(q.denominator))
    ff=lambda f:C.from_dict({(k[2],k[1],k[0]):rd(c) for k,c in f.items()})
    G=[ff(f) for f in gu]
    ds={}
    for k,v in raw.items():
        q=ff(v)
        while q:
            clean=False
            for p in G:
                if q%p:continue
                q=q//p;clean=True
            if not clean:break
        ds[k]=q
    return ds,G,ff(ZD),ff(ZN)

def regular_edge(mode):
    Q,G,ZD,ZN=edge_data(mode)
    C=flint.fmpq_mpoly_ctx.get(('a','b'))
    def co(f):
        assert not f.degrees()[0]
        return C.from_dict({(i,j):c for (u,j,i),c in f.to_dict().items()})
    zd,zn=map(co,(ZD,ZN))
    def calc(f):
        k=f.degrees()[0]
        return sum(C.from_dict({(i,l):c})*zn**j*zd**(k-j) for (j,l,i),c in f.to_dict().items())
    guard=[]
    for f in G+[ZD]:
        w=calc(f)
        if w and not w.is_constant():guard.append(w)
    res={}
    for k,f in Q.items():
        out=calc(f);tr=[]
        for i,p in enumerate(guard):
            while True:
                v=out.gcd(p)
                if v.is_constant():break
                out=out//v;tr.append((i,v.degrees()))
        res[k]=out
        print(mode,k,out.degrees(),tr,flush=True)
    return res,guard


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


def verify_edge_fibers(mode,widths):
    Fs,guards=regular_edge(mode)
    R,a,b=ring('a,b',QQ);W,X=ring('X',R);d=1-b;h=a/2;e=1-b/2
    v=X*(1-X)*(X-a)*(X-h)*(X-d)*(X-e)
    m0,m1,m2,m3,m4=[integ(v,j) for j in range(5)]
    H3=m0*(m2*m4-m3*m3)-m1*(m1*m4-m2*m3)+m2*(m1*m3-m2*m2)
    ctx=flint.fmpq_mpoly_ctx.get(('a','b'))
    guards.append(ctx.from_dict({k:flint.fmpq(int(v.numerator),int(v.denominator)) for k,v in H3.items()}))
    tests=[Fs[k] for k in ('G','F','R')]
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
    table={"matched":{108:(27,17,1),6:(26,11,2),9:(26,11,2)},"opposite":{132:(27,17,1),15:(26,11,2),6:(26,11,3)}}[mode]
    seen=set()
    for f,n in widths:
        F=flint.fmpq_poly(f);F=F/F[F.degree()]
        if not delta%F:continue
        deg=F.degree();i,j,n=table[deg];seen.add(deg)
        print("computing guard subresultant",mode,deg,i,j,flush=True)
        c=guards[i].gcd(guards[j])
        sr=into(guards[i]//c).subresultants(into(guards[j]//c))
        ls=[q for q in sr if q.degree()==1]
        assert ls
        lin=ls[-1]
        L=ac0(lin[(1,)])%F; Q=ac0(lin[(0,)])%F
        assert L
        testpol=[to_coeffs(f) for f in tests]
        gds=[to_coeffs(guards[k]) for k in (i,j)]
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



def verify_central():
    for branch,names,degrees in [
        ("singular",("delta","sN"),((36,0),(36,0))),
        ("regular",("F","g"),((36,0),(96,0)))]:
        _,_,polys,_=matched_center_shapes(branch)
        a,b=[polys["Cmat"].resultant(polys[n],"b") for n in names]
        assert (a.degrees(),b.degrees())==degrees and a.gcd(b).is_constant()
        print("central matched",branch,"exact constant width gcd",flush=True)
    rr=opposite_center_projections(("ML","MR","B","F"))
    assert [f.degrees() for k,f in rr]==[(0,630),(0,957),(0,718)]
    g=reduce(lambda a,b:a.gcd(b),[f for k,f in rr])
    _,a=g.context().gens()
    assert not g%(a**8) and (g//a**8).is_constant()
    print("central opposite exact width gcd a^8",flush=True)

def verify_singular_edge(mode):
    Q,G,E,N=edge_data(mode)
    C=flint.fmpq_mpoly_ctx.get(("b","a"))
    tr=lambda f:C.from_dict({(j,i):c for (k,j,i),c in f.to_dict().items()})
    def cut(p):
        for v in G[:11]:
            t=tr(v)
            while not p%t:p=p//t
        return p
    u,v=map(lambda f:cut(tr(f)),(E,N))
    assert u.gcd(v).is_constant()
    q=u.resultant(v,"b")
    assert q.degrees()==(0,18 if mode=="matched" else 32)
    for k in (("R",) if mode=="matched" else ("R","F")):
        r=Q["G"].resultant(Q[k],"z")
        assert not r.degrees()[0]
        q=q.gcd(u.resultant(tr(r),"b"))
    assert q.is_constant() and q
    print("edge",mode,"affine-zero exact constant width gcd",flush=True)

def verify_regular_edge(mode):
    R,_=regular_edge(mode)
    prim={k:irep(v) for k,v in R.items()}
    rs=exact(prim["G"],{k:prim[k] for k in ("F","R")})
    g=reduce(lambda a,b:a.gcd(b),rs.values())
    fs=g.factor()[1]
    if mode=="matched":
        assert [r.degree() for r in rs.values()]==[1081,611]
        assert sorted((f.degree(),n) for f,n in fs)==[(1,36),(6,10),(9,10),(108,1)]
    else:
        assert [r.degree() for r in rs.values()]==[1537,1048]
        assert sorted((f.degree(),n) for f,n in fs)==[(1,40),(1,108),(6,15),(15,10),(132,1)]
    print("edge",mode,"exact width gcd degree",g.degree(),flush=True)
    verify_edge_fibers(mode,fs)

if __name__=="__main__":
    verify_central()
    for mode in ("matched","opposite"):
        verify_singular_edge(mode)
        verify_regular_edge(mode)

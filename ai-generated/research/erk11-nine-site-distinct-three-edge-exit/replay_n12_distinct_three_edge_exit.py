"""Complete exact four-distinct three-cross edge exit.
Dependencies: SymPy and python-flint 0.9 / compatible.
All projections use exact coefficients, including characteristic-zero
unit-ideal lifts in whole coefficient algebras. No real-root scouting.
"""
from sympy import QQ
from sympy.polys.rings import ring
from functools import reduce
import flint
Nmat=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
T4=[1,-32,216,-480,330]
U4=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
def integ(f,j=0):return sum(c/(i[0]+j+1) for i,c in f.items())
def dot(g,h):return sum(g[i]*Nmat[i][j]*h[j] for i in range(5) for j in range(5))
def ev(cs,q):return sum(c*q**i for i,c in enumerate(cs))

def build():
    R,a,b=ring('a,b',QQ)
    W,X=ring('X',R)
    d=1-b;h=a/2;e=1-b/2
    Va=X**2*(X-a)**2
    Vb=(1-X)**2*(X-d)**2
    prim=lambda f:sum(c*X**(k[0]+1)/(k[0]+1) for k,c in f.items())
    P=prim(Va)
    q0=prim(Vb);Q=W(sum(q0.values()))-q0
    H=integ(P*Vb); C=integ(P*Vb,1);J=integ(P*Q)
    I0,I1,I2=[integ(Va*Vb,k) for k in range(3)]
    M=I1*H-I0*C; N=I2*H-I1*C
    I=I2*H*H-2*C*H*I1+C*C*I0
    hul=(X-a)*(X-h)*(X-d)*(X-e)*(H*X-C)
    m=[integ(X*(1-X)*hul,j) for j in range(4)]
    p,q,r=[M*m[j+1]-N*m[j] for j in range(3)]
    D=p*r-q*q
    L0=(a-e)*(a*p-q);L1=-e*q
    R0=(h-d)*(q-d*p);R1=-(1-h)*(p-q)
    l0=[R.one]+[R.zero]*4;l1=[(i+1)*a**i for i in range(5)]
    r0=[R.one]*5;r1=[d**i-(b*i*d**(i-1) if i else 0) for i in range(5)]
    phiL=[L0*u+L1*v for u,v in zip(l0,l1)]
    phiR=[R0*u+R1*v for u,v in zip(r0,r1)]
    F=dot(phiL,phiR)
    assert F==L0*R0+ev(T4,a)*L1*R0+ev(T4,b)*L0*R1+ev([ev(row,b) for row in U4],a)*L1*R1
    Pnum=N**3*(6*N*N-15*a*N*M+10*a*a*M*M)/30
    Qnum=sum(c*N**i[0]*M**(5-i[0]) for i,c in Q.items())
    Dz=[a**5*N**(i+1)*M**(4-i)-30*Pnum*a**(i+1) for i in range(5)]
    Rz=[(M-N)*N**i*M**(4-i) for i in range(5)]
    Ru=[(H-C)*C**i*H**(4-i) for i in range(5)]
    Rd=[b*d**i for i in range(5)]
    G=dot(Dz,phiR)
    Pool=dot(Dz,Ru)*dot(phiL,Rd)-dot(Dz,Rd)*dot(phiL,Ru)
    reversePort=I*dot(phiL,[b**5*v-30*Qnum*w for v,w in zip(Rz,Rd)])-30*J*H*(H*N-C*M)*(M-N)**2*(N-d*M)**2*dot(phiL,Rd)
    Amp=I*(N-h*M)*(N-e*M)*(p*N-q*M)*M*M+(p*m[1]-q*m[0])*N*(N-M)*(N-a*M)*(N-d*M)*(H*N-C*M)
    guards=[a,b,a-1,a-2,b-1,b-2,a+b-1,a+b-2,2*a+b-2,a+2*b-2,H,M,
            C,C-H,C-a*H,C-h*H,C-d*H,C-e*H,
            N,N-M,N-a*M,N-h*M,N-d*M,N-e*M,H*N-C*M,
            p,q,q-p,q-a*p,q-h*p,q-d*p,q-e*p,H*q-C*p,M*q-N*p,I,p*m[1]-q*m[0]]
    F0=[('D',D),('F',F),('G',G),('Pool',Pool),('Port',reversePort),('Amp',Amp)]
    ctx=flint.fmpq_mpoly_ctx.get(('a','b'))
    cu=lambda c:flint.fmpq(int(c.numerator),int(c.denominator))
    cv=lambda u:ctx.from_dict({k:cu(v) for k,v in u.items()})
    gu=[cv(u) for u in guards]
    out=[]
    for key,u in F0:
        f=cv(u);ls=[]
        for j,g in enumerate(gu):
            while True:
                h0=g.gcd(f)
                if h0.is_constant():break
                f=f//h0;ls.append((j,h0.degrees()))
        out.append((key,f,ls))
    return out,gu


from math import gcd,lcm,factorial,comb
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


def verify_fibers(widths):
    F0,guards=build()
    Fs={k:f for k,f,s in F0}
    tests=[Fs[k] for k in ('D','F','G')]
    ar,a=ring('a',QQ);br,b=ring('b',ar)
    def into(f):
        p={}
        for (i,j),c in f.to_dict().items():
            p.setdefault((int(j),),{})[(int(i),)]=QQ(int(c.numerator))/int(c.denominator)
        return br.from_dict({j:ar.from_dict(v) for j,v in p.items()})
    ac=lambda c:flint.fmpq(int(c.numerator),int(c.denominator))
    def ac0(u):
        return flint.fmpq_poly([ac(u.get((i,),QQ.zero)) for i in range(u.degree()+1)])
    def to_coeffs(f):
        s=into(f)
        return [ac0(s.get((i,),ar.zero)) for i in range(s.degree()+1)]
    A=flint.fmpq_poly([0,1]);delta=A*(A-1)*(A-2)
    table={72:(25,26,1),12:(11,18,2),8:(10,12,4)}
    seen=set()
    for f,n in widths:
        F=flint.fmpq_poly(f);F=F/F[F.degree()]
        if not delta%F:continue
        deg=F.degree();i,j,n=table[deg];seen.add(deg)
        sr=into(guards[i]).subresultants(into(guards[j]))
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


def mom(R,a,b):
    W,X=ring('X',R);d=1-b;h=a/2;e=1-b/2
    Va=X**2*(X-a)**2;Vb=(1-X)**2*(X-d)**2
    prim=lambda f:sum(c*X**(k[0]+1)/(k[0]+1) for k,c in f.items())
    P=prim(Va);Q0=prim(Vb);Q=W(sum(Q0.values()))-Q0
    H=integ(P*Vb);C=integ(P*Vb,1);J=integ(P*Q)
    I0,I1,I2=[integ(Va*Vb,j) for j in range(3)]
    return X,P,Q,Va,Vb,H,C,J,I0,I1,I2

def small(a,b,K):
    R,u=ring('u',K);a,b=R(a),R(b)
    X,P,Q,Va,Vb,H,C,J,I0,I1,I2=mom(R,a,b)
    assert not H and not C
    d=1-b;h=a/2;e=1-b/2
    M=I1-u*I0;N=I2-u*I1
    I=I2-2*u*I1+u*u*I0
    assert M and I
    P5=(X-a)*(X-h)*(X-d)*(X-e)*(X-u)
    m=[integ(X*(1-X)*P5,j) for j in range(4)]
    p,q,r=[M*m[j+1]-N*m[j] for j in range(3)]
    P1=p*r-q*q
    L0=(a-e)*(a*p-q);L1=-e*q
    R0=(h-d)*(q-d*p);R1=-(1-h)*(p-q)
    l0=[R.one]+[R.zero]*4
    l1=[(i+1)*a**i for i in range(5)]
    r0=[R.one]*5
    r1=[d**i-(b*i*d**(i-1) if i else 0) for i in range(5)]
    PL=[L0*v+L1*w for v,w in zip(l0,l1)]
    PR=[R0*v+R1*w for v,w in zip(r0,r1)]
    P2=dot(PL,PR)
    JP=N**3*(6*N*N-15*a*N*M+10*a*a*M*M)/30
    QP=sum(c*N**i[0]*M**(5-i[0]) for i,c in Q.items())
    Dz=[a**5*N**(i+1)*M**(4-i)-30*JP*a**(i+1) for i in range(5)]
    P3=dot(Dz,PR)
    Ru=[(1-u)*u**i for i in range(5)]
    Rd=[b*d**i for i in range(5)]
    Rz=[(M-N)*N**i*M**(4-i) for i in range(5)]
    P4=dot(Dz,Ru)*dot(PL,Rd)-dot(Dz,Rd)*dot(PL,Ru)
    P5b=I*dot(PL,[b**5*v-30*QP*w for v,w in zip(Rz,Rd)])-30*J*(N-u*M)*(M-N)**2*(N-d*M)**2*dot(PL,Rd)
    G=[M,N,N-M,N-a*M,N-h*M,N-d*M,N-e*M,N-u*M,p,q,q-p,q-a*p,q-h*p,q-d*p,q-e*p,q-u*p,M*q-N*p,I,p*m[1]-q*m[0],u,u-1,u-a,u-h,u-e,u-d]
    Ps=[P1,P2,P3,P4,P5b]
    assert all(Ps)
    g=P1.gcd(P2).gcd(P3)
    assert [v.degree() for v in Ps[:3]]==[4,4,7] and g.degree()==0
    print("zero H,C remaining u: raw gates degrees 4,4,7, exact gcd 1",flush=True)

def verify_zero_H():
    A,a=ring('a',QQ);B,b=ring('b',A)
    *_,H,C,J,I0,I1,I2=mom(B,B(a),b)
    proj=H.resultant(C)
    ds=proj.factor_list()[1]
    assert [(q.degree(),n) for q,n in ds]==[(8,1)]
    V=a.as_expr()
    for f,n in ds:
        if not (a*(a-1)*(a-2))%f:continue
        q=s.Poly(f.as_expr(),V,domain=QQ)
        assert q.is_irreducible
        K=QQ.algebraic_field(s.CRootOf(q,0));a1=K.unit
        R,b1=ring('b',K)
        *_,H1,C1,J,I0,I1,I2=mom(R,R(a1),b1)
        u=H1.gcd(C1).monic()
        print('zero H,C width',q.degree(),'second width gcd deg',u.degree(),flush=True)
        assert u.degree()==1
        b0=-u[(0,)]
        small(a1,b0,K)




def verify_live_H():
    pols,_=build()
    integs={k:irep(f) for k,f,tr in pols}
    rs=exact(integs["D"],{k:integs[k] for k in ("F","G")})
    assert [p.degree() for p in rs.values()]==[624,672]
    r=reduce(lambda f,g:f.gcd(g),rs.values())
    factors=r.factor()[1]
    assert r.degree()==280
    assert sorted((q.degree(),n) for q,n in factors)==[(1,32),(8,16),(12,4),(72,1)]
    assert next(f for f,n in factors if f.degree()==1)==flint.fmpz_poly([0,1])
    print("exact live-H width projection gcd degree 280",flush=True)
    verify_fibers(factors)

if __name__=="__main__":
    verify_zero_H()
    verify_live_H()

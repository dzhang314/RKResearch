"""Exact opposite-central ERK11 exit. By default recomputes all projections.
--fiber-only reuses the faithfully archived exact CRT factor checkpoint.
"""
from ast import literal_eval
from pathlib import Path
from math import lcm,gcd,factorial
import sympy as s
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
                assert i in (0,1) or (na=='QG' and i==17)
                assert h.degrees()==p.degrees() and not p%h
                f=f//h;st.append((i,h.degrees()))
        assert sum(i==17 for i,_ in st)==int(na=='QG')
        out[na]=f
        print(na,f.degrees(),st,flush=True)
    return out,guards,cv(N),cv(D)

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


P=flint.fmpq_poly

def co(f):
    d=f.to_dict(); da,db=f.degrees()
    return [P([d.get((i,j),0) for i in range(da+1)]) for j in range(db+1)]
def linear_candidates(f,g):
    h=f.gcd(g)
    R,a=ring('a',QQ);T,b=ring('b',R)
    def cv(f):
        return T.from_dict({(j,):R.from_dict({(i,):QQ(int(c.numerator))/int(c.denominator)
                                           for i,c in enumerate(r.coeffs())})
                            for j,r in enumerate(co(f)) if r})
    def into(g):
        return P([flint.fmpq(int(g.get((i,),0).numerator),int(g.get((i,),0).denominator))
                  for i in range(g.degree()+1)]) if g else P()
    S=cv(f//h).subresultants(cv(g//h))
    print('linear source b degrees',[q.degree() for q in S],flush=True)
    return [(into(x[(1,)]),into(x.get((0,),R.zero))) for x in S if x.degree()==1]

def verify(data0,fs):
    X,guards,N,E=data0
    names=('QG','RLR','RLG','RRG','QL','QR')
    paired=[X[k] for k in names]
    a=P([0,1]);forbidden=a*(a-2)
    lhs=linear_candidates(E,N)
    R0,ra,rb=ring('a,b',QQ);geo=model(R0,ra,rb);X0=geo['X']
    hull=(X0-ra)*(X0-ra/2)*(X0-geo['d'])*(X0-geo['e'])
    m=[integ(X0*(1-X0)*hull,j) for j in range(5)]
    Om=m[0]*(m[2]*m[4]-m[3]*m[3])-m[1]*(m[1]*m[4]-m[2]*m[3])+m[2]*(m[1]*m[3]-m[2]*m[2])
    C=flint.fmpq_mpoly_ctx.get(('a','b'))
    omega=C.from_dict({k:flint.fmpq(int(v.numerator),int(v.denominator)) for k,v in Om.items()})
    rhs=linear_candidates(omega,guards[17])
    for cs,n in fs:
        K=P(cs);K/=K[K.degree()];d=K.degree()
        if d==1:assert not forbidden%K;continue
        assert d in (2,6,15,132)
        power=1 if d==132 else 6 if d in (6,15) else 0
        bguard=[guards[k] for k in (17,20,21)] if d==132 else [E,N] if power else []
        print('running exact guards',d,flush=True)
        if power:
            cand=rhs if d==132 else lhs
            L,M=next((L%K,M%K) for L,M in reversed(cand) if L%K)
            l0=L.gcd(M)
            if l0.degree()>0:L,M=L//l0,M//l0
            # Both coefficients are scaled together, preserving the root.
            L,M=L/L[L.degree()],M/L[L.degree()]
            assert L.gcd(K).degree()==0
            print('guard linear degrees',d,L.degree(),M.degree(),flush=True)
        else:
            L,M=P([1]),P()
        trim=lambda vs: vs[:next((j+1 for j in reversed(range(len(vs))) if vs[j]),0)]
        T={k:trim([f%K for f in co(w)]) for k,w in zip(names,paired)}
        # Only evaluate the small guard polynomials homogeneously.
        # The raw norm/compatibility expressions in the proof establish
        # exact divisibility of all six width polynomials by the specified
        # power, and the reduction independently checks the quotient.
        for i,w in enumerate(bguard):
            cj=trim([f%K for f in co(w)]);n=len(cj)-1
            a0,b0=[P([1])],[P([1])]
            for _ in range(n):
                a0.append((a0[-1]*L)%K);b0.append((-b0[-1]*M)%K)
            he=sum((f*b0[j]*a0[n-j])%K for j,f in enumerate(cj))%K
            assert not he
            print('exact forbidden guard',d,i,flush=True)
        found=False
        for p in (107,103,109,113,127,131,137,139):
            try:
                Z=flint.fmpz_mod_poly_ctx(p)
                rd=lambda c:int(c.numerator)%p*pow(int(c.denominator),-1,p)%p
                F=Z([rd(c) for c in K.coeffs()])
                if F.degree()!=d or F.gcd(F.derivative()).degree():continue
                for h,_ in sorted(F.factor()[1],key=lambda kv:kv[0].degree()):
                    R=flint.fq_default_ctx(modulus=h,fq_type='FQ_NMOD')
                    U=flint.fq_default_poly_ctx(R);av=R.gen()
                    ap=[av**i for i in range(d)]
                    vv=lambda q:sum((R(rd(c))*t for c,t in zip(q.coeffs(),ap)),R.zero())
                    if not vv(L):continue
                    b0=-vv(M)/vv(L)
                    if power and (not av or not b0):continue
                    bf=U([-b0,R.one()])**power
                    Fp={k:U([vv(c) for c in T[k]]) for k in names}
                    assert all(not f%bf for f in Fp.values())
                    kept={k:f//bf for k,f in Fp.items()}
                    live=[k for k,f in kept.items() if f and f.degree()==len(T[k])-1-power]
                    if not live or reduce(lambda a,b:a.gcd(b),kept.values()).degree():continue
                    found=True
                    print('whole one-place unit lift',d,p,h.degree(),live,flush=True);break
                if found:break
            except (ZeroDivisionError,ValueError):
                continue
        assert found
    print('All characteristic-zero opposite-central width fibers close.',flush=True)

def run(use_checkpoint=False):
    W=data('opposite')
    fs=literal_eval(Path(__file__).with_name('opposite-central-width-factors.txt').read_text())
    assert sorted((len(cs)-1,n) for cs,n in fs)==[(1,138),(1,456),(2,8),(2,8),(6,42),(15,42),(132,2)]
    got=flint.fmpz_poly([1])
    for cs,n in fs:
        f=flint.fmpz_poly(cs)
        assert [(g.degree(),m) for g,m in f.factor()[1]]==[(f.degree(),1)]
        got*=f**n
    assert got.degree()==1772
    if use_checkpoint:
        print('Using the archived exact projection checkpoint.',flush=True)
    else:
        T=W[0]
        pr=exact(irep(T['QG']),{k:irep(T[k]) for k in ('RLR','RLG')})
        assert [f.degree() for f in pr.values()]==[3808,3812]
        R=pr['RLR'].gcd(pr['RLG'])
        assert R.degree()==1772 and R.gcd(got).degree()==1772
    verify(W,fs)

if __name__=='__main__':
    from sys import argv
    run('--fiber-only' in argv[1:])

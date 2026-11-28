"""Complete exact four-distinct three-cross central exit.
Requires SymPy and python-flint 0.9 or compatible. The long part
is deterministic coefficient-bounded integer CRT on three explicit
symmetric width resultants. No file data or numerical guesses required.
"""
from math import comb
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
    R,a,b,u=ring('a,b,u',QQ)
    W,X=ring('X',R)
    d=1-b;h=a/2;e=1-b/2
    Va=X**2*(X-a)**2;Vb=(1-X)**2*(X-d)**2
    prim=lambda f:sum(c*X**(k[0]+1)/(k[0]+1) for k,c in f.items())
    P=prim(Va);Q0=prim(Vb);Q=W(sum(Q0.values()))-Q0
    H=integ(P*Vb);C1=integ(P*Vb,1);C2=integ(Va*Q,1);J=integ(P*Q)
    assert H==integ(Va*Q) and J==C1-C2
    I0,I1,I2=[integ(Va*Vb,j) for j in range(3)]
    M=I1-u*I0;N=I2-u*I1;I=N-u*M
    LL=(C1-u*H)*(C2-u*H)-J*I
    P5=(X-a)*(X-h)*(X-d)*(X-e)*(X-u)
    mom=[integ(X*(1-X)*P5,j) for j in range(4)]
    p,q,r=[M*mom[j+1]-N*mom[j] for j in range(3)]
    D=p*r-q*q
    L0=(a-e)*(a*p-q);L1=-e*q
    R0=(h-d)*(q-d*p);R1=-(1-h)*(p-q)
    l0=[R.one]+[R.zero]*4;l1=[(i+1)*a**i for i in range(5)]
    r0=[R.one]*5;r1=[d**i-(b*i*d**(i-1) if i else 0) for i in range(5)]
    PL=[L0*v+L1*w for v,w in zip(l0,l1)]
    PR=[R0*v+R1*w for v,w in zip(r0,r1)]
    F=dot(PL,PR)
    assert F==L0*R0+ev(T4,a)*L1*R0+ev(T4,b)*L0*R1+ev([ev(row,b) for row in U4],a)*L1*R1
    numP=N**3*(6*N*N-15*a*N*M+10*a*a*M*M)/30
    numQ=sum(c*N**i[0]*M**(5-i[0]) for i,c in Q.items())
    Vl=N**2*(N-a*M)**2;Vr=(M-N)**2*(N-d*M)**2
    lAa=[a**(i+1) for i in range(5)];rDd=[b*d**i for i in range(5)]
    LH=[a**5*N**(i+1)*M**(4-i)+30*((C1-u*H)*Vl-numP)*c for i,c in enumerate(lAa)]
    RH=[b**5*(M-N)*N**i*M**(4-i)+30*((C2-u*H)*Vr-numQ)*c for i,c in enumerate(rDd)]
    diag=210*dot(LH,RH)-a**5*b**5*I*Vl*Vr
    amp=M*M*(N-h*M)*(N-e*M)*(p*N-q*M)+(p*mom[1]-q*mom[0])*N*(N-M)*(N-a*M)*(N-d*M)
    guard=[a,b,a-1,a-2,b-1,b-2,a+b-1,a+b-2,2*a+b-2,a+2*b-2,u,u-1,u-a,u-h,u-d,u-e,
           M,N,N-M,N-a*M,N-h*M,N-d*M,N-e*M,I,
           p,q,q-p,q-a*p,q-h*p,q-d*p,q-e*p,q-u*p,M*q-N*p,p*mom[1]-q*mom[0]]
    raw={'L':LL,'D':D,'F':F,'A':amp,'B':diag}
    return raw,guard

def flint_data(names):
    R,G=build();C=flint.fmpq_mpoly_ctx.get(('u','b','a'))
    cv=lambda c:flint.fmpq(int(c.numerator),int(c.denominator))
    to=lambda p:C.from_dict({(k[2],k[1],k[0]):cv(c) for k,c in p.items()})
    Q={k:to(R[k]) for k in set(names)|{"L"}};Gs=list(map(to,G))
    def trim(f):
        # Divide only exact divisors of proven-live guarded polynomials.
        stats=[]
        for i,g in enumerate(Gs):
            while True:
                if f%g:break
                stats.append((i,g.degrees()));f=f//g
        return f,stats
    return C,{k:trim(v) for k,v in Q.items()},Gs

def norm_projection(names):
    C,Q,G=flint_data(names)
    a=flint.fmpq_mpoly_ctx.get(('a','b'))
    L=Q["L"][0]
    assert L.degrees()[0]==2 and not Q['L'][1]
    rems={}
    for name in names:
        print(name,'shape',Q[name][0].degrees(),'trim',Q[name][1],flush=True)
        f=L.resultant(Q[name][0],'u')
        assert not f.degrees()[0]
        r=a.from_dict({(k[2],k[1]):c for k,c in f.to_dict().items()})
        print('  raw norm',r.degrees(),flush=True)
        rems[name]=r
    return rems



def symmetric_transform(q, CT, swapped=False):
    s,p=CT.gens()
    if swapped:s,p=p,s
    assert all(c==q.get((j,i),0) for (i,j),c in q.items())
    ps=[CT.constant(2),s]
    for j in range(2,81):ps.append(s*ps[-1]-p*ps[-2])
    return sum(c*p**j*(ps[i-j] if i>j else 1) for (i,j),c in q.items() if i>=j)

def symmetric_data():
    names=("D","F","A","B")
    R=norm_projection(names)
    C=flint.fmpq_mpoly_ctx.get(("s","p"))
    s,p=C.gens()
    g=[s-1,s-2,p,p-s+1,p-2*s+4,p+2*(s-2)*(s-1)]
    out={}
    for k,f in R.items():
        q=symmetric_transform(f.to_dict(),C)
        for v in g:
            while not q%v:q=q//v
        out[k]=q
    assert [f.degrees() for f in out.values()]==[(32,32),(40,40),(50,50),(52,52)]
    return out

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
        D=flint.nmod_mpoly_ctx.get(('p','s'),p)
        lift=lambda T:D.from_dict({(j,i):v%p for (i,j),v in T.items()})
        A=lift(prim)
        rhs={k:lift(f) for k,f in rest.items()}
        if A.degrees()[0]!=dz(prim) or any(rhs[k].degrees()[0]!=dz(rest[k]) for k in rhs):continue
        mp=pow(M%p,-1,p)
        for k,T in rhs.items():
            R=A.resultant(T,'p')
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


R,a,b=ring('a,b',QQ);S,X=ring('X',R);d=1-b
Va=X**2*(X-a)**2;Vb=(1-X)**2*(X-d)**2
P=X**3*(6*X*X-15*a*X+10*a*a)/30
H=integ(P*Vb);C1=integ(P*Vb,1)
Q0=sum(v*X**(j[0]+1)/(j[0]+1) for j,v in Vb.items())
Q=S(sum(Q0.values()))-Q0
C2=integ(Va*Q,1);J=integ(P*Q)
I0,I1,I2=[integ(Va*Vb,j) for j in range(3)]
A=H*H-J*I0;B=2*J*I1-H*(C1+C2);C=C1*C2-J*I2
F=flint.fmpq_mpoly_ctx.get(('b','a'))
cv=lambda p:F.from_dict({(j,i):flint.fmpq(int(v.numerator),int(v.denominator)) for (i,j),v in p.items()})
G=[cv(x) for x in (A,B,C)]
rr=[G[i].resultant(G[j],'b') for i,j in [(0,1),(0,2),(1,2)]]
gg=reduce(lambda s,t:s.gcd(t),rr)
assert [r.degrees() for r in rr]==[(0,32),(0,28),(0,26)] and gg.is_constant() and gg


# Exact low-degree origin of the nonzero p-root on the degree-12 s-factor.
Pctx=flint.fmpq_mpoly_ctx.get(("p","s"))
cu=lambda c:flint.fmpq(int(c.numerator),int(c.denominator))
Zs=symmetric_transform({k:cu(v) for k,v in (I0*I2-I1**2).items()},Pctx,True)
Vs=symmetric_transform({k:cu(v) for k,v in ((C1*I0-H*I1)*(C2*I0-H*I1)).items()},Pctx,True)
proj=Zs.resultant(Vs,"p")
assert proj.degrees()==(0,28)

FP=flint.fmpq_poly
SP=FP([0,1])
f12=next(f for f,k in proj.factor()[1] if f.degrees()[1]==12)
W12=FP([f12.to_dict().get((0,i),0) for i in range(13)])
W12=W12/W12[12]
W4=165*SP**4-264*SP**3+156*SP*SP-40*SP+4
W4=W4/W4[4]

def pivot12():
    S,s=ring('s',QQ);R,p=ring('p',S)
    def into(f):
        box={}
        for (j,i),c in f.to_dict().items():
            box.setdefault((int(j),),{})[(int(i),)]=QQ(int(c.numerator))/int(c.denominator)
        return R.from_dict({k:S.from_dict(u) for k,u in box.items()})
    gs=list(map(into,[Zs,Vs]))
    sr=[f for f in gs[0].subresultants(gs[1]) if f.degree()==1][-1]
    cu=lambda c:flint.fmpq(int(c.numerator),int(c.denominator))
    lift=lambda f:FP([cu(f.get((i,),QQ.zero)) for i in range(f.degree()+1)])
    L=lift(sr[(1,)])%W12;N=lift(sr[(0,)])%W12
    assert L
    for g in gs:
        degree=g.degree()
        assert not sum((lift(v)*(-N)**i[0]*L**(degree-i[0]))%W12 for i,v in g.items())%W12
    return L,N

def p_quotient(Q,W,L,N,n=2,prime=101):
    def co(g):
        k=g.degrees()[1];v=[{} for _ in range(k+1)]
        for (i,j),c in g.to_dict().items():v[j][i]=c
        return [FP([w.get(j,0) for j in range(max(w,default=0)+1)])%W for w in v]
    Ps=list(map(co,Q.values()))
    maxp=max(len(p) for p in Ps)
    lp=[FP([1])];np=lp[:]
    for _ in range(maxp):
        lp.append((lp[-1]*L)%W);np.append((-np[-1]*N)%W)
    for P in Ps:
        for i in range(n):
            assert not sum((comb(j,i)*P[j]*np[j-i]*lp[len(P)-1-j])%W for j in range(i,len(P)))%W
    K0=flint.fmpz_mod_poly_ctx(prime)
    rd=lambda c:int(c.numerator)%prime*pow(int(c.denominator),-1,prime)%prime
    cv=lambda f:K0([rd(c) for c in f.coeffs()])
    assert cv(L).gcd(cv(W)).degree()==0 and cv(W).degree()==W.degree()
    degs=set(range(len(Ps)))
    for f,k in cv(W).factor()[1]:
        assert k==1
        K=flint.fq_default_ctx(modulus=f,fq_type='FQ_NMOD')
        R=flint.fq_default_poly_ctx(K);t=K.gen()
        cp=lambda w:sum((K(rd(c))*t**i for i,c in enumerate(w.coeffs())),K.zero())
        u=R([cp(N)/cp(L),K.one()])**n
        quot=[]
        for s in Ps:
            c=R([cp(q) for q in s]);assert not c%u;quot.append(c//u)
        degs&={i for i,s in enumerate(quot) if s.degree()==len(Ps[i])-1-n}
        assert reduce(lambda s,t:s.gcd(t),quot).degree()==0
        print('p-fiber mod',prime,'degree',f.degree(),'quotient ideal unit',flush=True)
    assert degs
    return sorted(degs)

def final_u_quotient(L,N,prime=101):
    # Symbolic u coefficient lists after cancelling u-u0 structurally.
    R=H.ring;a,b=R.gens
    T,u=ring('u',R)
    W,X=ring('X',T)
    a,b=T(a),T(b);d=1-b;h=a/2;e=1-b/2
    A=H*H-J*I0;B=2*J*I1-H*(C1+C2)
    ell=T(I0*A)*u+T(I0*B+A*I1)
    P5=(X-a)*(X-h)*(X-d)*(X-e)*(X-u)
    m=[integ(X*(1-X)*P5,i) for i in range(4)]
    p,q,r=[T(I0)*m[i+1]-T(I1)*m[i] for i in range(3)]
    D=p*r-q*q
    L0=(a-e)*(a*p-q);L1=-e*q
    R0=(h-d)*(q-d*p);R1=-(1-h)*(p-q)
    F=L0*R0+ev(T4,a)*L1*R0+ev(T4,b)*L0*R1+ev([ev(z,b) for z in U4],a)*L1*R1
    K0=flint.fmpz_mod_poly_ctx(prime)
    rd=lambda c:int(c.numerator)%prime*pow(int(c.denominator),-1,prime)%prime
    cv=lambda f:K0([rd(c) for c in f.coeffs()])
    Mf=cv(W12)
    total=0
    for f,k in Mf.factor()[1]:
        d=f.degree();assert k==1
        K=flint.fq_default_ctx(prime,2*d,'w',fq_type='FQ_NMOD')
        P=flint.fq_default_poly_ctx(K)
        Y=P([K.zero(),K.one()])
        sf=P([K(int(c)) for c in f.coeffs()])
        for root,si in sf.factor()[1]:
            assert si==1 and root.degree()==1
            s=-root[0]
            cp=lambda z:sum((K(rd(c))*s**i for i,c in enumerate(z.coeffs())),K.zero())
            z=-cp(N)/cp(L)
            aq=Y**2-s*Y+z
            for Tt,ii in aq.factor()[1]:
                assert Tt.degree()==1 and ii==1
                a=-Tt[0];b=s-a;total+=1
                def v(r):
                    return sum((K(rd(c))*a**i*b**j for (i,j),c in r.items()),K.zero())
                assert v(I0) and v(A)
                fromu=lambda r:P([v(r.get((i,),R.zero)) for i in range(r.degree()+1)])
                assert fromu(ell).degree()==1
                assert reduce(lambda f,h:f.gcd(h),map(fromu,(ell,D,F))).degree()==0
            print('u-fiber over s component degree',d,'unit for all a widths',flush=True)
    assert total==24



def main():
    P=symmetric_data()
    L,N=pivot12()
    p_quotient(P,W4,FP([1]),FP([]))
    p_quotient(P,W12,L,N)
    final_u_quotient(L,N)
    B={k:irep(v) for k,v in P.items()}
    D=exact(B["D"],{k:B[k] for k in ("F","A","B")})
    assert [v.degree() for v in D.values()]==[1264,1568,1632]
    g=FP(reduce(lambda a,b:a.gcd(b),D.values()))
    assert g.degree()==80 and g/g[80]==W4**8*W12**4
    print("exact monic projection gcd W4^8 W12^4 of degree 80",flush=True)

if __name__=="__main__":main()

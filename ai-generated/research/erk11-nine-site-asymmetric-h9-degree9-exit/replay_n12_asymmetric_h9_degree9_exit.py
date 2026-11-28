"""Exact regular-residue proof for a canonical h9 width factor."""
from math import lcm,gcd
from scipy.optimize import linear_sum_assignment
import numpy as np
"""Exact finite width atlas, canonically asymmetric h@9 dormant edge."""
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
Gram = N

def data():
    R,va,vb,vz=ring('a,b,z',QQ);W=model(R,va,vb);X=W['X'];h0,d0,e0=[W[k] for k in ('h','d','e')]
    C=flint.fmpq_mpoly_ctx.get(('z','b','a'));z,b,a=C.gens();rd=lambda x:flint.fmpq(int(x.numerator),int(x.denominator))
    cv=lambda f:C.from_dict({(k,j,i):rd(v) for (i,j,k),v in f.items()})
    h,d,e,A,B0,C0,D0,H,J,C1,C2,I0,I1,I2=[cv(W[k]) for k in ('h','d','e','A','B','C','D','H','J','C1','C2','I0','I1','I2')]
    E=A*z+C0;N=-(B0*z+D0)
    P4=(X-va)*(X-h0)*(X-d0)*(X-e0);m=[cv(integ(X*(1-X)*P4,j)) for j in range(5)]
    M=[m[j+1]-z*m[j] for j in range(4)]
    D=M[0]*M[2]-M[1]*M[1];S=M[0]*M[3]-M[1]*M[2];P=M[1]*M[3]-M[2]*M[2]
    U=D*E;T=S*E-D*N
    Q=D*N*N-S*N*E+P*E*E
    R0=d*d*D-d*S+P;R1=-D+S-P
    L0=(a-e)*(a*U-T);L1=-e*T
    F=L0*R0+cv(ev(T4,va))*L1*R0+cv(ev(T4,vb))*L0*R1+cv(ev([ev(r,vb) for r in U4],va))*L1*R1
    K=lambda x,p,q:sum(cv(v)*p**j[0]*q**(3-j[0]) for j,v in x.items())
    G=R0*K(W['Ks'][0],z,C.constant(1))+R1*K(W['Ks'][1],z,C.constant(1))
    Mark=L0*K(W['Ms'][0],N,E)+L1*K(W['Ms'][1],N,E)
    Arow=[R0*cv(v)+R1*cv(w) for v,w in zip(W['dr0'],W['dr1'])];Aa=list(map(cv,W['el'](va)))
    Ra=sum(Aa[i]*Gram[i][j]*Arow[j] for i in range(5) for j in range(5))
    L=a*(C2-z*H)*(R0*K(W['Ks'][0],h,C.constant(1))+R1*K(W['Ks'][1],h,C.constant(1)))+30*h*(a-h)*(h-z)*J*Ra
    I=E*I2-(h*E+N)*I1+h*N*I0
    Om=m[0]*P-m[1]*S+m[2]*D;assert Om.degrees()[0]==0
    Support=I*(z-e)*(z*U-T)-Om*E*E*z*(1-z)*(z-a)*(z-d)
    guards=[cv(f) for f in W['known'][:10]]+[E,D,Om,I]+[z-u for u in [0,1,a,h,d,e]]
    guards += [N-u*E for u in (0,1,a,h,d,e,z)]+[T-u*U for u in (0,1,a,h,d,e,z)]+[N*U-E*T,S*S-4*D*P]
    raw={'F':F,'G':G,'R':Mark,'L':L,'Q':Q,'S':Support}
    for k,f in raw.items():
        for g in guards:
            while f:
                v=f.gcd(g)
                if v.is_constant(): break
                f=f//v
        raw[k]=f;print('gate',k,f.degrees(),flush=True)
    return raw,guards

def raw():
 D,gs=data();S,sa,sb,sz=ring('a,b,z',QQ);W=model(S,sa,sb)
 C=flint.fmpq_mpoly_ctx.get(('z','b','a'));z,b,a=C.gens();rd=lambda q:flint.fmpq(int(q.numerator),int(q.denominator))
 cv=lambda f:C.from_dict({(k,j,i):rd(v) for (i,j,k),v in f.items()})
 h,e,d,A,B0,C0,D0,H,J,C2=[cv(W[k]) for k in ('h','e','d','A','B','C','D','H','J','C2')]
 E=A*z+C0;N=-(B0*z+D0)
 hh=lambda f,y,p:sum(cv(c)*y**j[0]*p**(3-j[0]) for j,c in f.items())
 k0,k1=[hh(f,z,C.constant(1)) for f in W['Ks']]
 m0,m1=[hh(f,N,E) for f in W['Ms']]
 Arow=W['el'](sa)
 dot=lambda r,s:sum(r[i]*Gram[i][j]*s[j] for i in range(5) for j in range(5))
 u=30*h*(a-h)*(h-z)*J
 c=[a*(C2-z*H)*hh(k,h,C.constant(1))+u*cv(dot(Arow,r)) for k,r in zip(W['Ks'],(W['dr0'],W['dr1']))]
 ta,tb,xy=map(cv,(ev(T4,sa),ev(T4,sb),ev([ev(r,sb) for r in U4],sa)))
 D['M']=k0*c[1]-k1*c[0]
 D['K']=m1*k1-ta*m0*k1-tb*m1*k0+xy*m0*k0
 for k in 'MK':
    f=D[k];vv=[]
    for i,g in enumerate(gs):
        while f:
            w=f.gcd(g)
            if w.is_constant():break
            f=f//w;vv.append((i,w.degrees()))
    D[k]=f;print('SMALL',k,f.degrees(),vv,flush=True)
 return D,gs

def project(base,keys):
 D,gs=raw();C=flint.fmpq_mpoly_ctx.get(('b','a'));w=lambda f:C.from_dict({(j,i):v for (k,j,i),v in f.to_dict().items()})
 G=[w(f) for f in gs if not f.degrees()[0]];out={};t=monotonic()
 for k in keys:
    f=w(D[base].resultant(D[k],0))
    for g in G:
        while f:
            v=f.gcd(g)
            if v.is_constant():break
            f=f//v
    out[k]=f
    print('WIDTH',base+k,f.degrees(),round(monotonic()-t,2),flush=True)
    if len(out)>1:
        g=reduce(lambda a,b:a.gcd(b),out.values());print('gcd',g.degrees(),[(f.degrees(),n) for f,n in g.factor()[1]],flush=True)
 return out



def primitive(q):
    d=q.to_dict();L=lcm(*(int(v.denominator) for v in d.values()))
    d={i:int(v.numerator)*(L//int(v.denominator)) for i,v in d.items()}
    g=gcd(*d.values())
    return {i:v//g for i,v in d.items()}

Q=flint.fmpq_poly

def coeffs(f):
    d=f.to_dict();m,n=f.degrees()
    return [Q([d.get((i,j),0) for j in range(n+1)]) for i in range(m+1)]

def syl(V,W,zero):
    m,n=len(V)-1,len(W)-1
    N=m+n
    return [[zero]*i+V+[zero]*(N-i-m-1) for i in range(n)]+[[zero]*i+W+[zero]*(N-i-n-1) for i in range(m)]

def scales(M):
    d=np.asarray([[p.degree() if p else -1000000 for p in line] for line in M],dtype='int64')
    rows,perm=linear_sum_assignment(d,maximize=True)
    assert all(i==j for i,j in enumerate(rows))
    pairs=d[rows,perm]
    assert min(pairs)>=0
    n=len(M);v=np.zeros(n,dtype='int64')
    for j in range(n):
        z=(v[perm,None]+d-pairs[:,None]).max(axis=0)
        if np.all(z==v):break
        v=np.maximum(v,z)
    u=pairs-v[perm]
    assert np.all(u[:,None]+v[None,:]>=d)
    return int(pairs.sum()),[int(x) for x in u],[int(x) for x in v]

def valuation_ge(M,target):
    n=len(M);v=r=0;cols=[];t=monotonic();logs=[]
    while v<target:
        for top,k in enumerate(cols):
            den=M[top][k][0]
            for i in range(r,n):
                n0=M[i][k][0]
                if n0:
                    c=n0/den
                    M[i]=[f-c*g if g else f for f,g in zip(M[i],M[top])]
        for k in range(n):
            if k in cols: continue
            p=next((i for i in range(r,n) if M[i][k][0]),None)
            if p is None:continue
            M[r],M[p]=M[p],M[r];den=M[r][k][0]
            for i in range(r+1,n):
                n0=M[i][k][0]
                if n0:
                    c=n0/den
                    M[i]=[f-c*g if g else f for f,g in zip(M[i],M[r])]
            cols.append(k);r+=1
        if r==n:return v,logs
        for i in range(r,n):
            assert not any(f[0] for f in M[i])
            M[i]=[f.right_shift(1) for f in M[i]]
        v+=n-r;logs.append(n-r)
        print('valuation progress',v,'nullity',n-r,'sec',round(monotonic()-t,2),flush=True)
    return v,logs

def top(f,g,d):
    M=syl(coeffs(f),coeffs(g),Q())
    upper,u,v=scales(M)
    print('degree upper',upper,'required vanishing at infinity',upper-d,flush=True)
    if upper==d:return
    n=len(M);G=[];goal=upper-d
    for i,row in enumerate(M):
        G.append([Q() if not p else Q([p[u[i]+v[j]-k] if u[i]+v[j]>=k else 0
                                       for k in range(goal+1)]) for j,p in enumerate(row)])
    vl,l=valuation_ge(G,goal);assert vl>=goal


def certify(bdegree=9,p=103):
    assert flint.fmpz(p).is_prime()
    P=project('M','GQFS')
    Z=project('G','QF')
    D,_guards=raw()
    fs=P.pop('G').factor()[1]
    assert sorted((f.degrees(),j) for f,j in fs)==[((3,6),2),((9,12),1),((31,35),1)]
    W=next(f for f,_ in fs if f.degrees()[0]==bdegree)
    P.update({'Z'+k:v for k,v in Z.items()})
    mod=flint.nmod_mpoly_ctx.get(('b','a'),p)
    ModA=flint.fmpz_mod_poly_ctx(p)
    w=lambda f:mod.from_dict({ij:v%p for ij,v in primitive(f).items()})
    ww=w(W);assert ww.degrees()[0]==bdegree
    res={}
    for k in ('Q','F','ZQ','ZF'):
        v=w(P[k]);assert v.degrees()[0]==P[k].degrees()[0]
        R=ww.resultant(v,0)
        assert R
        res[k]=R
        print('projection',k,R.degrees(),flush=True)
    rg=reduce(lambda x,y:x.gcd(y),res.values())
    rf=ModA([int(rg.to_dict().get((0,i),0))%p for i in range(rg.degrees()[1]+1)])
    factors=rf.factor()[1]
    print('a gcd',rf.degree(),'factors',[(g.degree(),n) for g,n in factors],flush=True)
    failures=[]
    for q,_ in factors:
        C=flint.fq_default_ctx(modulus=q,fq_type='FQ_NMOD')
        B=flint.fq_default_poly_ctx(C)
        a=C.gen()
        def lift(f):
            f=primitive(f)
            ds=[C.zero() for _ in range(max(i for i,_ in f)+1)]
            ps=[a**j for j in range(max(j for _,j in f)+1)]
            for (i,j),v in f.items():ds[i]+=C(v%p)*ps[j]
            return B(ds)
        W0=lift(W)
        g=reduce(lambda u,f:u.gcd(lift(f)),P.values(),W0)
        print('residue a degree',q.degree(),'pivot degree b',W0.degree(),'b gcd degree',g.degree(),flush=True)
        if W0.degree()!=bdegree:failures.append(('width',q.degree(),g.degree()));continue
        for bf,n in g.factor()[1]:
            if bf.degree()!=1:failures.append(('higher b degree',q.degree(),bf.degree()));continue
            b=-bf[0]/bf[1]
            def evaluate(f):
                f=primitive(f)
                z=[C.zero() for _ in range(max(k for k,_,_ in f)+1)]
                ax=[a**i for i in range(max(i for _,_,i in f)+1)]
                bx=[b**j for j in range(max(j for _,j,_ in f)+1)]
                for (k,j,i),u in f.items():z[k]+=C(u%p)*ax[i]*bx[j]
                return B(z)
            h={k:evaluate(f) for k,f in D.items()}
            piv=[k for k,f in h.items() if f.degree()==D[k].degrees()[0]]
            z=reduce(lambda u,v:u.gcd(v),h.values())
            print('at common b residue: full z degrees',piv,'z gcd',z.degree(),flush=True)
            if not piv or z.degree()!=0:failures.append(('dormant',q.degree(),z.degree()))
    print('failures',failures,flush=True)
    if not failures:
        top(W,P['Q'],res['Q'].degrees()[1])
        print('Finite integral residue tower contradiction in characteristic zero.',flush=True)
    return failures

if __name__=='__main__':
    assert not certify(9,103)

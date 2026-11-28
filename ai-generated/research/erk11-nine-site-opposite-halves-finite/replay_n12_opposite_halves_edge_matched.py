'''Exact characteristic-zero matched-edge exit, using an integral determinant degree certificate.

Dependencies: Python 3, sympy, python-flint, numpy, scipy.  Arithmetic in the
certificate is exact. scipy only proposes integer Sylvester scaling weights;
the replay checks the actual inequalities before they are used.
'''
from sympy import QQ
from sympy.polys.rings import ring
from functools import reduce
from math import lcm,gcd
from time import monotonic
from scipy.optimize import linear_sum_assignment
import numpy as np
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
def build(pos,orient):
    R,a,b,z=ring('a,b,z',QQ);W=model(R,a,b);X=W['X']
    h,e,d,A,B,C,D,H,C1,C2,J,I0,I1,I2=[W[k] for k in ('h','e','d','A','B','C','D','H','C1','C2','J','I0','I1','I2')]
    P4=(X-a)*(X-h)*(X-e)*(X-d)
    ms=[integ(X*(1-X)*P4,j) for j in range(5)]
    m=[ms[j+1]-z*ms[j] for j in range(4)]
    D2=m[0]*m[2]-m[1]*m[1];SN=m[0]*m[3]-m[1]*m[2];PN=m[1]*m[3]-m[2]*m[2]
    fit=D2*X**2-SN*X+PN
    hull=P4*fit
    H3=ms[0]*PN-ms[1]*SN+ms[2]*D2
    assert H3.degrees()[2]==0 and H3==integ(X*(1-X)*hull)
    vv=lambda w:w*(1-w)*(a-w)*(w-d)
    jc=lambda w:-sum(c*w**j/((i[0]-j+1)*(i[0]-j+2)) for i,c in hull.items() for j in range(i[0]))
    cr=(vv(h)*((h-z)*jc(h)-H3)*(e-z)-vv(e)*((e-z)*jc(e)-H3)*(h-z)).exquo(h-e)
    Ta,Tb,U=ev(T4,a),ev(T4,b),ev([ev(row,b) for row in U4],a)
    W2,t,s=ring('t,s',R);cv=lambda a:W2(a)
    L0=cv(a-e)*(cv(a)-t);L1=-cv(e)*t
    R0=cv(h-d)*(s-cv(d));R1=-cv(1-h)*(1-s)
    F=L0*R0+cv(Ta)*L1*R0+cv(Tb)*L0*R1+cv(U)*L1*R1
    x,y=(t,s) if orient=='matched' else (s,t)
    P0=cv(A)*x*y+cv(B)*x+cv(C)*y+cv(D) if pos=='center' else cv(A*z+C)*y+cv(B*z+D)
    def row(f):
        dij=lambda i,j:f.get((i,j),0)
        return dij(1,0)-dij(0,1),D2*dij(0,0)+SN*dij(0,1)+PN*dij(1,1)
    Uf,Vf=row(F);Up,Vp=row(P0)
    resultant=Uf*Vp-Up*Vf
    norm=lambda u,v:v*v+SN*u*v+D2*PN*u*u
    NF,NP=norm(Uf,Vf),norm(Up,Vp)
    root=lambda w:D2*w*w-SN*w+PN
    guards=W['known'][:10]+[z,z-1,z-a,z-h,z-d,z-e,H3,D2,SN*SN-4*D2*PN]
    guards += [root(w) for w in (0,1,a,h,d,e,z)]
    return {'X':cr,'D':resultant,'F':NF,'B':NP,'G':Vf,'H':Vp},guards,(Uf,Vf,Up,Vp,D2,SN,PN)


def data():
    p,gu,rows=build('edge','matched');UF=rows[0]
    R=UF.ring;va,vb,vs=R.gens
    W=model(R,va,vb);X=W['X']
    C=flint.fmpq_mpoly_ctx.get(('s','b','a'))
    rd=lambda v:flint.fmpq(int(v.numerator),int(v.denominator))
    cv=lambda f:C.from_dict({(k,j,i):rd(v) for (i,j,k),v in f.items()});s,b,a=C.gens()
    h,e,d,A,B0,C0,D0,J,H,I0,I1,I2=[cv(W[k]) for k in ('h','e','d','A','B','C','D','J','H','I0','I1','I2')]
    Ta,Tb=map(cv,(ev(T4,va),ev(T4,vb)));U=cv(ev([ev(r,vb) for r in U4],va));rank=(U-Ta*Tb)//(a*b)
    zD=A*s+B0;zN=-(C0*s+D0)
    P4=(X-va)*(X-W['h'])*(X-W['e'])*(X-W['d'])
    m=[cv(integ(X*(1-X)*P4,i)) for i in range(5)]
    M=[zD*m[i+1]-zN*m[i] for i in range(4)]
    tD=M[1]-s*M[0];tN=M[2]-s*M[1]
    Q=tD*(M[3]-s*M[2])-tN*tN
    R0=(h-d)*(s-d);R1=-(1-h)*(1-s)
    L0=(a-e)*(a*tD-tN);L1=-e*tN
    F0=R0+Tb*R1;F1=Ta*R0+U*R1
    norms=lambda u,y,v:sum(cv(c)*y**j[0]*v**(3-j[0]) for j,c in u.items())
    G=R0*norms(W['Ks'][0],zN,zD)+R1*norms(W['Ks'][1],zN,zD)
    K=F0*norms(W['Ms'][1],s,1)-F1*norms(W['Ms'][0],s,1)
    N=F0*L0+F1*L1
    H4=lambda f:sum(C.from_dict({(0,j,i):rd(c)})*zN**k*zD**(4-k) for (i,j,k),c in f.items())
    SUP=H4(p['X']);helm=lambda f:sum(C.from_dict({(0,j,i):rd(c)})*zN**k*zD**(f.degrees()[2]-k) for (i,j,k),c in f.items())
    guard=[cv(f) for f in gu[:10]]+[J,H,rank,cv(UF),zD,tD]+[wD*(value)-wN for value in [0,1,a,h,d,e,s] for wD,wN in ((zD,zN),(tD,tN))]
    guard+=[zN*tD-zD*tN,I2*tD-(tN+s*tD)*I1+s*tN*I0,helm(gu[16]),*[s-v for v in (0,1,a,h,d,e)]]
    out={'G':G,'K':K,'Q':Q,'F':N,'X':SUP}
    for k,f in out.items():
        for g in guard:
            while f:
                c=f.gcd(g)
                if c.is_constant():break
                f=f//c
        out[k]=f
        print('gate',k,f.degrees(),flush=True)
    return out,guard

def project():
    D,G=data();t=monotonic();C=flint.fmpq_mpoly_ctx.get(('b','a'))
    wd=lambda f:C.from_dict({(j,i):q for (k,j,i),q in f.to_dict().items()})
    guards=[wd(f) for f in G if not f.degrees()[0]]
    out={}
    for k in 'KQFX':
        f=wd(D['G'].resultant(D[k],0))
        for g in guards:
            while f:
                q=f.gcd(g)
                if q.is_constant():break
                f=f//q
        out[k]=f
        print('proj',k,f.degrees(),round(monotonic()-t,2),flush=True)
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

def finite(f,g,a,d):
    T=Q([a,1]);V,W=coeffs(f),coeffs(g)
    M=syl([p(T).truncate(d+1) for p in V],[p(T).truncate(d+1) for p in W],Q())
    return valuation_ge(M,d)





def certify():
    G=project()
    assert {k:g.degrees() for k,g in G.items()}=={'K':(32,28),'Q':(58,60),'F':(51,53),'X':(52,61)}
    p=103
    C=flint.nmod_mpoly_ctx.get(('b','a'),p)
    pk={k:C.from_dict({ij:v%p for ij,v in primitive(g).items()}) for k,g in G.items()}
    assert all(pk[k].degrees()[0]==G[k].degrees()[0] for k in G)
    R={k:pk['K'].resultant(pk[k],0) for k in ('Q','X')}
    assert {k:r.degrees() for k,r in R.items()}=={'Q':(0,3544),'X':(0,3408)}
    a=C.gens()[1]
    assert R['Q'].gcd(R['X'])==(a-2)**46
    for k,r in R.items():
        upper,*_=scales(syl(coeffs(G['K']),coeffs(G[k]),Q()))
        assert upper==r.degrees()[1]
        val,trace=finite(G['K'],G[k],2,46)
        assert val>=46
        print(k,'characteristic-zero degree',upper,'exact (a-2) power witness',trace,flush=True)
    print('Exact degrees and both common-factor lifts verified.',flush=True)

if __name__=='__main__':
    certify()

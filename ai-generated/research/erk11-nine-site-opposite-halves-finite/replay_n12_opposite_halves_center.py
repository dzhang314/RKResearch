'''Exact characteristic-zero central exit, both inner orientations, using an integral determinant degree certificate.

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


def data(pos,orient,p=None):
    D0,guard,rows=build(pos,orient)
    U0,V0,UB,VB,Ds,Ss,Ps=rows
    R=Ds.ring;Wa,Wb,Wz=R.gens
    W=model(R,Wa,Wb)
    if p:
        C=flint.nmod_mpoly_ctx.get(('Y','z','b','a'),p)
        T=flint.nmod_mpoly_ctx.get(('z','b','a'),p)
        rd=lambda x:int(x.numerator)%p*pow(int(x.denominator),-1,p)%p
    else:
        C=flint.fmpq_mpoly_ctx.get(('Y','z','b','a'))
        T=flint.fmpq_mpoly_ctx.get(('z','b','a'))
        rd=lambda x:flint.fmpq(int(x.numerator),int(x.denominator))
    Y,z,b,a=C.gens()
    cv=lambda f:C.from_dict({(0,k,j,i):rd(v) for (i,j,k),v in f.items()})
    uf,vf,ub,vb,Δ,σ,π=map(cv,rows)
    h,e,d,H,C1,C2,J,I0,I1,I2=[cv(W[k]) for k in ('h','e','d','H','C1','C2','J','I0','I1','I2')]
    sn=σ-Y
    lt,rs,zz=(Y,Δ),(sn,Δ),(z,C.constant(1))
    x,y=(lt,rs) if orient=='matched' else (rs,lt)
    L0=(a-e)*(a*Δ-Y);L1=-e*Y
    R0=(h-d)*(sn-d*Δ);R1=-(1-h)*(Δ-sn)
    Lrow=[L0*cv(aa)+L1*cv(bb) for aa,bb in zip(W['dl0'],W['dl1'])]
    Rrow=[R0*cv(aa)+R1*cv(bb) for aa,bb in zip(W['dr0'],W['dr1'])]
    dot=lambda r,s:sum(r[i]*N[i][j]*s[j] for i in range(5) for j in range(5))
    ra=dot(list(map(cv,W['el'](Wa))),Rrow);ld=dot(Lrow,list(map(cv,W['er'](W['d']))))
    hc=lambda f,x:sum(cv(c)*x[0]**i[0]*x[1]**(3-i[0]) for i,c in f.items())
    k=lambda x:R0*hc(W['Ks'][0],x)+R1*hc(W['Ks'][1],x)
    ell=lambda x:L0*hc(W['Ms'][0],x)+L1*hc(W['Ms'][1],x)
    ix=lambda x,y:I2*x[1]*y[1]-I1*(x[0]*y[1]+x[1]*y[0])+I0*x[0]*y[0]
    df=lambda x,y:x[0]*y[1]-x[1]*y[0]
    af=lambda c,x:c*x[1]-H*x[0]
    vh=lambda x:a*x[1]-x[0]
    wh=lambda x:(x[1]-x[0])*(x[0]-d*x[1])
    M={}
    if pos=='center':
        if orient=='matched':M={'L':k(lt),'R':ell(rs)}
        else:
            M={'L':a*ix(x,zz)*k(lt)+30*Y*vh(lt)*df(lt,x)*af(C1,zz)*ra,
               'R':b*ix(y,zz)*ell(rs)+30*wh(rs)*df(rs,y)*af(C2,zz)*ld}
    else:
        M['G']=k(zz)
        if orient=='matched':
            M['L']=a*af(C2,zz)*k(lt)+30*Y*vh(lt)*df(lt,zz)*J*ra
            M['R']=ell(rs)
        else:
            M['L']=a*ix(zz,x)*k(lt)+30*Y*vh(lt)*df(lt,zz)*af(C1,x)*ra
            M['R']=b*af(C1,y)*ell(rs)+30*wh(rs)*df(rs,y)*J*ld
        M['P']=b*ix(x,y)*ell(zz)+30*af(C2,x)*df(zz,y)*wh(zz)*ld
    q=Y*Y-σ*Y+Δ*π
    co=lambda f,j:C.from_dict({(0,k,l,m):v for (i,k,l,m),v in f.to_dict().items() if i==j})
    foot=lambda f:T.from_dict({(k,l,m):v for (i,k,l,m),v in f.to_dict().items()})
    out={k:cv(v) for k,v in D0.items()};GG=list(map(cv,guard))+[uf]
    for k,f in M.items():
        r=f%q
        assert r.degrees()[0]<2
        U,V=co(r,1),co(r,0)
        out['F'+k]=uf*V-U*vf
        out['B'+k]=ub*V-U*vb
        out['N'+k]=V*V+σ*U*V+Δ*π*U*U
    for k,f in out.items():
        for g in GG:
            while f:
                w=f.gcd(g)
                if w.is_constant():break
                f=f//w
        out[k]=foot(f)
        print('gate',k,f.degrees(),flush=True)
    return out,list(map(foot,GG))

def project(pos,orient,prime,base,keys):
    t=monotonic();d,gu=data(pos,orient,prime)
    W=(flint.nmod_mpoly_ctx.get(('b','a'),prime) if prime else flint.fmpq_mpoly_ctx.get(('b','a')))
    width=lambda f:W.from_dict({(j,i):v for (k,j,i),v in f.to_dict().items()})
    gs=[width(f) for f in gu if f and not f.degrees()[0]]
    P={}
    for k in keys:
        r=d[base].resultant(d[k],0)
        assert r and r.degrees()[0]==0
        r=width(r)
        for g in gs:
            while r:
                w=r.gcd(g)
                if w.is_constant():break
                r=r//w
        P[k]=r
        print('res',k,r.degrees(),round(monotonic()-t,2),flush=True)
        if len(P)>1:
            q=reduce(lambda x,y:x.gcd(y),P.values())
            print('common',q.degrees(),[(f.degrees(),n) for f,n in q.factor()[1]],flush=True)
    return P,gs,d

def sym(f):
    C=flint.fmpq_mpoly_ctx.get(('T','S'));T,S=C.gens();D=f.to_dict()
    power=[C.constant(2),S]
    n=max(f.degrees())
    for j in range(2,n+1):power.append(S*power[-1]-T*power[-2])
    for e,c in D.items():assert c==D.get(e[::-1],0),('asym',e,c,D.get(e[::-1],0))
    return sum(c*(T**j if i==j else T**j*power[i-j]) for (i,j),c in D.items() if i>=j)

def primitive(q):
    d=q.to_dict();L=lcm(*(int(v.denominator) for v in d.values()))
    d={i:int(v.numerator)*(L//int(v.denominator)) for i,v in d.items()}
    g=gcd(*d.values())
    return {i:v//g for i,v in d.items()}

def widths(orient):
    G,guards,_=project('center',orient,None,'D',('X','F','FL','FR'))
    W=G['FL'].context()
    sw=lambda f:W.from_dict({(j,i):c for (i,j),c in f.to_dict().items()})
    X=G['FL'];Y=sw(X)
    assert not Y%G['FR'] and (Y//G['FR']).is_constant()
    return {k:sym(f/f.leading_coefficient()) for k,f in G.items() if k in ('X','F')}|{'M':sym(X+Y)}

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



def certify(orientation):
    G=widths(orientation)
    ints={k:primitive(f) for k,f in G.items()}
    p=107 if orientation=='matched' else 103
    C=flint.nmod_mpoly_ctx.get(('T','S'),p)
    R={k:C.from_dict({ij:v%p for ij,v in pol.items()}) for k,pol in ints.items()}
    assert all(R[k].degrees()[0]==G[k].degrees()[0] for k in G)
    proj={k:R['F'].resultant(R[k],0) for k in ('X','M')}
    expected={'X':(0,1820),'M':(0,2544)} if orientation=='matched' else {'X':(0,1960),'M':(0,3384)}
    assert {k:v.degrees() for k,v in proj.items()}==expected
    S=C.gens()[1]
    assert proj['X'].gcd(proj['M'])==((S-2)**8 if orientation=='matched' else C.constant(1))
    for k,R0 in proj.items():
        print(orientation,'exact determinant degree:',k,R0.degrees()[1],flush=True)
        top(G['F'],G[k],R0.degrees()[1])
        if orientation=='matched':
            val,trace=finite(G['F'],G[k],2,8)
            assert val>=8
            print('lifted (S-2)^8 exact rank witness',k,trace,flush=True)
    print(orientation,'degree preservation and gcd implication checked.',flush=True)

if __name__=='__main__':
    from sys import argv
    for orientation in (argv[1:] or ['matched','opposite']):
        assert orientation in ('matched','opposite')
        certify(orientation)

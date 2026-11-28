"""Exact residue lifting for the large mirrored width component."""
from math import gcd,lcm
from scipy.optimize import linear_sum_assignment
import numpy as np
"""Exact mirrored asymmetric edge finite atlas, both mixed determinant ranks."""
from sympy import QQ
from sympy.polys.rings import ring
from functools import reduce
from math import lcm,gcd
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
Gram=N

Nmat = Gram
def raw():
 R,va,vb,vz=ring('a,b,z',QQ);W=model(R,va,vb);X=W['X'];h0,e0,d0=[W[k] for k in ('h','e','d')]
 C=flint.fmpq_mpoly_ctx.get(('z','b','a'));rd=lambda c:flint.fmpq(int(c.numerator),int(c.denominator));z,b,a=C.gens()
 cv=lambda f:C.from_dict({(k,j,i):rd(v) for (i,j,k),v in f.items()})
 h,e,d,A,B0,C0,D0,H,J,C1,C2,I0,I1,I2=[cv(W[k]) for k in ('h','e','d','A','B','C','D','H','J','C1','C2','I0','I1','I2')]
 E=A*z+C0;N=-(B0*z+D0)
 P4=(X-va)*(X-h0)*(X-e0)*(X-d0);m=[cv(integ(X*(1-X)*P4,i)) for i in range(5)];M=[m[i+1]-z*m[i] for i in range(4)]
 D=M[0]*M[2]-M[1]*M[1];S=M[0]*M[3]-M[1]*M[2];P=M[1]*M[3]-M[2]*M[2]
 Omega=m[0]*P-m[1]*S+m[2]*D;assert Omega.degrees()[0]==0
 T=S*E-D*N;U=D*E
 Q=D*N*N-S*N*E+P*E*E
 L0=a*a*D-a*S+P;L1=-P
 R0=(h-d)*(T-d*U);R1=-(1-h)*(U-T)
 F=L0*R0+cv(ev(T4,va))*L1*R0+cv(ev(T4,vb))*L0*R1+cv(ev([ev(r,vb) for r in U4],va))*L1*R1
 h3=lambda f,y,p:sum(cv(c)*y**i[0]*p**(3-i[0]) for i,c in f.items())
 Z=C.constant(1)
 G=R0*h3(W['Ks'][0],z,Z)+R1*h3(W['Ks'][1],z,Z)
 Arow=[R0*cv(v)+R1*cv(w) for v,w in zip(W['dr0'],W['dr1'])]
 dot=lambda r,s:sum(r[i]*Nmat[i][j]*s[j] for i in range(5) for j in range(5))
 Ra=dot(list(map(cv,W['el'](va))),Arow)
 ie=I2-(z+e)*I1+z*e*I0
 P10=a*ie*(R0*h3(W['Ks'][0],N,E)+R1*h3(W['Ks'][1],N,E))+30*N*(a*E-N)*(N-z*E)*(C1-e*H)*Ra
 I=E*I2-(e*E+N)*I1+e*N*I0
 Dd=W['er'](d0);Dl=(W['dl0'],W['dl1'])
 ell=[cv(dot(f,Dd)) for f in Dl]
 rowe=[b*(E*C1-N*H)*h3(k,e,Z)+30*(1-e)*(e-d)*(e*E-N)*J*l for k,l in zip(W['Ms'],ell)]
 rowz=[b*I*h3(k,z,Z)+30*(C2-e*H)*(z*E-N)*(1-z)*(z-d)*l for k,l in zip(W['Ms'],ell)]
 test=rowz[0]*rowe[1]-rowz[1]*rowe[0]
 assert not test%(z-e)
 Sout=I*(z-h)*(z*U-T)-Omega*E*E*z*(1-z)*(z-a)*(z-d)
 guards=[cv(f) for f in W['known'][:10]]+[E,D,Omega,I]+[z-v for v in (0,1,a,h,d,e)]
 guards += [N-v*E for v in (0,1,a,h,d,e,z)]+[T-v*U for v in (0,1,a,h,d,e,z)]+[N*U-E*T,S*S-4*D*P]
 ta,tb,U4ab=map(cv,(ev(T4,va),ev(T4,vb),ev([ev(r,vb) for r in U4],va)))
 k0,k1=[h3(f,z,Z) for f in W['Ks']]
 x0,x1=rowe
 K=x1*k1-ta*x0*k1-tb*x1*k0+U4ab*x0*k0
 Dx=k0*(tb*L0+U4ab*L1)-k1*(L0+ta*L1)
 V={'Q':Q,'F':F,'G':G,'M':test,'E':L0*rowe[0]+L1*rowe[1],'P':L0*rowz[0]+L1*rowz[1],'S':Sout,'L':P10,'K':K,'D':Dx}
 for k,f in V.items():
  gg=[]
  for i,s in enumerate(guards):
   while f:
    v=f.gcd(s)
    if v.is_constant():break
    f=f//v;gg.append((i,v.degrees()))
  V[k]=f;print('gate',k,f.degrees(),gg,flush=True)
 return V,guards

def project(base,which):
 V,G=raw();C=flint.fmpq_mpoly_ctx.get(('b','a'));w=lambda f:C.from_dict({(j,i):v for (k,j,i),v in f.to_dict().items()});W=[w(f) for f in G if not f.degrees()[0]]
 ans={};s=monotonic()
 for k in which:
  f=w(V[base].resultant(V[k],0))
  for g in W:
   while f:
    q=f.gcd(g)
    if q.is_constant():break
    f=f//q
  ans[k]=f;g=reduce(lambda a,b:a.gcd(b),ans.values());print('width',base+k,f.degrees(),'common',g.degrees(),round(monotonic()-s,2),flush=True)
 return ans

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

def top(f,g,d,slots,expected):
    M=syl(coeffs(f),coeffs(g),Q())
    upper,u,v=scales(M)
    print('degree upper',upper,'required vanishing at infinity',upper-d,flush=True)
    if upper==d:return
    n=len(M);G=[];goal=upper-d
    for i,row in enumerate(M):
        G.append([Q() if not p else Q([p[u[i]+v[j]-k] if u[i]+v[j]>=k else 0
                                       for k in range(slots)]) for j,p in enumerate(row)])
    vl,L=valuation_ge(G,goal);assert vl>=goal and (expected is None or L==expected) and len(L)<=slots


def independent():
    R,va,vb,vz=ring('a,b,z',QQ);W=model(R,va,vb);X=W['X'];h0,e0,d0=[W[k] for k in ('h','e','d')]
    C=flint.fmpq_mpoly_ctx.get(('Y','z','b','a'));Y,z,b,a=C.gens();rd=lambda x:flint.fmpq(int(x.numerator),int(x.denominator))
    cv=lambda f:C.from_dict({(0,k,j,i):rd(v) for (i,j,k),v in f.items()})
    h,e,d,A,B0,C0,D0,H,J,C1,C2,I0,I1,I2=[cv(W[k]) for k in ('h','e','d','A','B','C','D','H','J','C1','C2','I0','I1','I2')]
    E=A*e+B0;N=-(C0*e+D0)
    P4=(X-va)*(X-h0)*(X-d0)*(X-e0);m=[cv(integ(X*(1-X)*P4,j)) for j in range(5)]
    M=[m[j+1]-z*m[j] for j in range(4)]
    D=M[0]*M[2]-M[1]*M[1];S=M[0]*M[3]-M[1]*M[2];P=M[1]*M[3]-M[2]*M[2]
    O=m[0]*P-m[1]*S+m[2]*D;assert not O.degrees()[1]
    L0=a*a*D-a*S+P;L1=-P
    R0=(h-d)*(Y-d*D);R1=-(1-h)*(D-Y)
    Ta,Tb,V=cv(ev(T4,va)),cv(ev(T4,vb)),cv(ev([ev(r,vb) for r in U4],va))
    first=L0*R0+Ta*L1*R0+Tb*L0*R1+V*L1*R1
    at=lambda f,x:sum(cv(v)*x**j[0] for j,v in f.items())
    G=L0*at(W['Ms'][0],e)+L1*at(W['Ms'][1],e)
    port=R0*at(W['Ks'][0],z)+R1*at(W['Ks'][1],z)
    sn=S-Y;hc=lambda f:sum(cv(v)*sn**j[0]*D**(3-j[0]) for j,v in f.items())
    rr=[R0*cv(v)+R1*cv(w) for v,w in zip(W['dr0'],W['dr1'])];aa=list(map(cv,W['el'](va)))
    ra=sum(aa[i]*Gram[i][j]*rr[j] for i in range(5) for j in range(5))
    Mark=a*(C2-z*H)*(R0*hc(W['Ks'][0])+R1*hc(W['Ks'][1]))+30*sn*(a*D-sn)*(sn-z*D)*J*ra
    Us=-(z-h)*(I2-e*I1+(e*I0-I1)*z)
    Vs=(z-h)*((I2-e*I1)*z*D+(e*I0-I1)*(z*S-P))-O*z*(1-z)*(z-a)*(z-d)
    q=Y*Y-S*Y+D*P
    k=lambda f,n:C.from_dict({(0,z,j,i):v for (y,z,j,i),v in f.to_dict().items() if y==n})
    row=lambda f:(k(f%q,1),k(f%q,0))
    u0,v0=row(first);u1,v1=row(port);u2,v2=row(Mark)
    Norm=lambda u,v:v*v+S*u*v+D*P*u*u
    gates={'G':G,'F':Norm(u0,v0),'P':u0*v1-u1*v0,'N':Norm(u1,v1),'S':u0*Vs-Us*v0,'T':Norm(Us,Vs),'M':u0*v2-u2*v0}
    guard=[cv(f) for f in W['known'][:10]]+[O,D,S*S-4*D*P]+[z-u for u in (0,1,a,h,d,e)]
    guard += [D*u*u-S*u+P for u in (0,1,a,h,d,e,z)]
    P3=flint.fmpq_mpoly_ctx.get(('z','b','a'));px=lambda f:P3.from_dict({(z,j,i):v for (y,z,j,i),v in f.to_dict().items()})
    gs=list(map(px,guard));out={}
    for k,f in gates.items():
        f=px(f);dropped=[]
        for i,g in enumerate(gs):
            while f:
                w=f.gcd(g)
                if w.is_constant():break
                f=f//w;dropped.append((i,w.degrees(),bool(w%g)))
        assert all(i in range(10) or (i==11 and not partial) for i,d,partial in dropped)
        assert sum(i==11 for i,_,_ in dropped)==(1 if k in ('F','P','N','M') else 0)
        print('raw',k,f.degrees(),dropped,flush=True);out[k]=f
    return out,gs,px(E),px(N)

def certify():
    D,_=raw();A0,*_=independent()
    for k in ('F','P','N','S','T'):D['A'+k]=A0[k]
    W=project('D','KQE')
    c=flint.fmpq_mpoly_ctx.get(('b','a'));R,a,b=ring('a,b',QQ);Q0=model(R,a,b)
    r33=(ev([ev(row,b) for row in U4],a)-ev(T4,a)*ev(T4,b)).exquo(a*b)
    cv=lambda f:c.from_dict({(j,i):flint.fmpq(int(v.numerator),int(v.denominator)) for (i,j),v in f.items()})
    for k,w in W.items():
        for h in [cv(Q0['J']),cv(r33)]:
            while w:
                g=w.gcd(h)
                if g.is_constant():break
                w=w//g
        W[k]=w
    fac=W.pop('K').factor()[1]
    assert sorted((x.degrees(),u) for x,u in fac)==[((9,12),1),((51,54),1)]
    F=next(f for f,j in fac if f.degrees()==(51,54))
    p=103;assert flint.fmpz(p).is_prime()
    C=flint.nmod_mpoly_ctx.get(('b','a'),p);Z=flint.nmod_mpoly_ctx.get(('z','b','a'),p)
    T=flint.fmpz_mod_poly_ctx(p)
    redw=lambda f:C.from_dict({k:v%p for k,v in primitive(f).items()})
    redz=lambda f:Z.from_dict({k:v%p for k,v in primitive(f).items()})
    f=redw(F);V={k:redw(w) for k,w in W.items()}
    assert f.degrees()==F.degrees() and V['Q'].degrees()==W['Q'].degrees()
    A=f.resultant(V['Q'],0);B=f.resultant(V['Q'],1)
    assert A.degrees()==(0,7620) and B.degrees()==(7609,0)
    h=A
    for k in ('F','P','AN'):
        r,z=redz(D['D']),redz(D[k])
        assert r.degrees()[0]==D['D'].degrees()[0] and z.degrees()[0]==D[k].degrees()[0]
        rz=r.resultant(z,0)
        assert all(i==0 for i,_,_ in rz.to_dict())
        V['D'+k]=C.from_dict({(j,i):v for (z,j,i),v in rz.to_dict().items()})
        rr=f.resultant(V['D'+k],0);h=h.gcd(rr)
        print('projection',k,rr.degrees(),'gcd',h.degrees(),flush=True)
    print('last residue a gcd',h,flush=True)
    hx=h.to_dict();ha=T([int(hx.get((0,j),0)) for j in range(h.degrees()[1]+1)])
    bx=B.to_dict()
    hb=T([int(bx.get((i,0),0)) for i in range(B.degrees()[0]+1)])
    assert ha.monic()==T([-1,1])
    # Keep the projection unaltered: its mod-103 b^2 factor is
    # accidental and no division by it in characteristic zero is used.
    for q,_ in ha.factor()[1]:
        R=flint.fq_default_ctx(modulus=q,fq_type='FQ_NMOD')
        P=flint.fq_default_poly_ctx(R);a=R.gen()
        def u(f):
            oo=[R.zero()]*(f.degrees()[0]+1);aa=[a**i for i in range(f.degrees()[1]+1)]
            for (j,i),k in f.to_dict().items():oo[j]+=R(int(k))*aa[i]
            return P(oo)
        j=reduce(lambda x,y:x.gcd(u(y)),V.values(),u(f))
        j=j.gcd(P([R(c) for c in hb.coeffs()]))
        print('last b gcd',j,flush=True)
        assert j.degree()==0
    top(F,W['Q'],7620,5,[12,12,4,4,4])
    Cv=flint.fmpq_mpoly_ctx.get(('a','b'))
    sw=lambda f:Cv.from_dict({(j,i):v for (i,j),v in f.to_dict().items()})
    top(sw(F),sw(W['Q']),7609,3,[23,23,1])
    print('Whole mirrored (51,54) width component excluded; no finite b residue.',flush=True)

if __name__=='__main__':certify()

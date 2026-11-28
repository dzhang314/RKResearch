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
def build():
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

def zero_exit():
 D,G,_,_=build();R,a,b,z=ring('a,b,z',QQ);M=model(R,a,b);C=flint.fmpq_mpoly_ctx.get(('z','b','a'));W=flint.fmpq_mpoly_ctx.get(('b','a'))
 cv=lambda f:C.from_dict({(k,j,i):flint.fmpq(int(v.numerator),int(v.denominator)) for (i,j,k),v in f.items()});wd=lambda f:W.from_dict({(j,i):v for (k,j,i),v in f.to_dict().items()})
 E,N=cv(M['A']*z+M['C']),cv(-M['B']*z-M['D']);G=[wd(f) for f in G if not f.degrees()[0]]
 Eall={'E':E,'N':N};ls={}
 for y,v in Eall.items():
  for k in 'FPNST':
   f=wd(v.resultant(D[k],0))
   for p in G:
    while f:
     q=f.gcd(p)
     if q.is_constant():break
     f=f//q
   ls[y+k]=f;print(y+k,f.degrees(),flush=True)
 R33=(ev([ev(r,b) for r in U4],a)-ev(T4,a)*ev(T4,b)).exquo(a*b)
 assert 633719116800000*(M['A']*M['D']-M['B']*M['C'])==-a*a*b*b*M['J']*R33
 for name,x in [('J',M['J']),('R33',R33)]:
  v=wd(cv(x));g=None
  for k,f in ls.items():
   r=v.resultant(f,0);g=r if g is None else g.gcd(r);print(name,k,r.degrees(),g.degrees(),flush=True)
   if g.is_constant():break
  assert g.is_constant()
  print('exceptions',name,[(f.degrees()[1],j) for f,j in g.factor()[1]],flush=True)

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
 dot=lambda r,s:sum(r[i]*Gram[i][j]*s[j] for i in range(5) for j in range(5))
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
 V={'Q':Q,'F':F,'G':G,'M':test,'E':L0*rowe[0]+L1*rowe[1],'P':L0*rowz[0]+L1*rowz[1],'S':Sout,'L':P10}
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

def rank_data():
 R,va,vb=ring('a,b',QQ);W=model(R,va,vb);X=W['X'];h,e,d=[W[k] for k in ('h','e','d')]
 A=W['A'];N=-W['B'];J=W['J'];K=W['C1']
 Ta,Tb=ev(T4,va),ev(T4,vb);U0=ev([ev(r,vb) for r in U4],va);R33=(U0-Ta*Tb).exquo(va*vb)
 hull5=(X-va)*(X-h)*(X-e)*(X-d)*(A*X-N);m=[integ(X*(1-X)*hull5,j) for j in range(4)]
 D=m[0]*m[2]-m[1]*m[1];S=m[0]*m[3]-m[1]*m[2];P=m[1]*m[3]-m[2]*m[2]
 C=flint.fmpq_mpoly_ctx.get(('Y','b','a'));Y,b,a=C.gens();rd=lambda q:flint.fmpq(int(q.numerator),int(q.denominator))
 cv=lambda f:C.from_dict({(0,j,i):rd(v) for (i,j),v in f.items()});E,N,H,J,K,ta,tb,u,rr=map(cv,(A,N,W['H'],J,K,Ta,Tb,U0,R33))
 D,S,P,h,e,d=map(cv,(D,S,P,h,e,d));z=S-Y
 L0=(a*E-N)*(a*D-Y);L1=-N*Y
 R0=(h-d)*(Y-d*D);R1=-(1-h)*(D-Y)
 F=L0*R0+ta*L1*R0+tb*L0*R1+u*L1*R1
 hc=lambda f,y,v:sum(cv(c)*y**j[0]*v**(3-j[0]) for j,c in f.items())
 G=R0*hc(W['Ks'][0],z,D)+R1*hc(W['Ks'][1],z,D)
 dd=W['er'](W['d']);dot=lambda p,q:sum(p[i]*Gram[i][j]*q[j] for i in range(5) for j in range(5));lb=[cv(dot(r,dd)) for r in (W['dl0'],W['dl1'])]
 row=[b*(E*K-N*H)*hc(f,e,C.constant(1))+30*(1-e)*(e-d)*(e*E-N)*J*l for f,l in zip(W['Ms'],lb)]
 M=L0*row[0]+L1*row[1]
 I=E*cv(W['I2'])-(e*E+N)*cv(W['I1'])+e*N*cv(W['I0'])
 M0,M1=map(cv,m[:2])
 X0=I*(z-h*D)*(z-Y)*D**3-(M1*D-M0*Y)*z*(D-z)*(z-a*D)*(z-d*D)
 c0=lambda f,j:C.from_dict({(0,k,i):v for (y,k,i),v in f.to_dict().items() if y==j})
 Q=Y*Y-S*Y+D*P
 Norm=lambda f:(lambda u,v:v*v+S*u*v+D*P*u*u)(c0(f%Q,1),c0(f%Q,0))
 g0={'F':Norm(F)}
 gu=[cv(v) for v in W['known'][:10]]+[E,D,S*S-4*D*P]
 gu += [N-v*E for v in (0,1,a,h,d,e)]+[D*v*v-S*v+P for v in (0,1,a,h,d,e)]+[D*N*N-S*N*E+P*E*E]
 CC=flint.fmpq_mpoly_ctx.get(('b','a'));wd=lambda f:CC.from_dict({(j,i):v for (k,j,i),v in f.to_dict().items()});out={}
 for k,f in g0.items():
  rm=[]
  for i,g in enumerate(gu):
   while f:
    s=f.gcd(g)
    if s.is_constant():break
    f=f//s;rm.append((i,s.degrees()))
  print(k,f.degrees(),rm,flush=True);out[k]=wd(f)
 return out,{'J':wd(J),'R':wd(rr),'A':wd(E)}



def certify():
    zero_exit()
    W=project('E','QG')
    F,R=rank_data()
    assert {k:v.degrees() for k,v in W.items()}=={'Q':(74,70),'G':(98,99)}
    for k,g in W.items():
        for j in ('J','R'):
            while True:
                w=g.gcd(R[j])
                if w.is_constant():break
                g=g//w
        W[k]=g
    assert {k:v.degrees() for k,v in W.items()}=={'Q':(60,56),'G':(83,84)}
    assert W['Q'].gcd(W['G']).is_constant()
    print('rank-live regular widths: exact coprime bidegrees (60,56),(83,84)',flush=True)
    assert F['F'].degrees()==(38,40)
    for j in ('J','R'):
        assert R[j].gcd(F['F']).is_constant()
        assert R[j].gcd(R['A']).is_constant()
    print('rank-zero widths: exact J/R33 intersections with both first norm and A are finite.',flush=True)

if __name__=='__main__':
    certify()

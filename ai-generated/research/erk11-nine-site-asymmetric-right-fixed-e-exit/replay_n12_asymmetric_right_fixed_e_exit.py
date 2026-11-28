"""Exact asymmetric edge, right chooser and fixed right half.
Python 3, sympy and python-flint. Run default for both exact global and local
parts, or --fiber-only with the independently exact cached factor list."""
from pathlib import Path
from ast import literal_eval
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

def width_guards(q,g,E,N):
    W=flint.fmpq_mpoly_ctx.get(('b','a'));cv=lambda f:W.from_dict({(j,i):v for (k,j,i),v in f.to_dict().items()})
    def clean(f,gu):
        for w in gu:
            while f and w:
                d=f.gcd(w)
                if d.is_constant():break
                f=f//d
        return f
    return W,cv,clean

def zero():
    Q,guards,E,N=build();W,px,clean=width_guards(Q,guards,E,N)
    gu=[px(f) for f in guards if not f.degrees()[0]]
    e,n=clean(px(E),gu),clean(px(N),gu)
    p=e.resultant(n,0);assert p.degrees()==(0,18);lst=[p]
    for k in 'FPNS':
        f=clean(px(Q['G'].resultant(Q[k],0)),gu)
        r=e.resultant(f,0);lst.append(r)
        gg=reduce(lambda a,b:a.gcd(b),lst)
        print('zero',k,p.degrees(),r.degrees(),gg.degrees(),[(f.degrees(),n) for f,n in gg.factor()[1]],flush=True)
        assert r.degrees()[1]=={'F':266,'P':277,'N':484,'S':0}[k]
        if gg.is_constant():break
    assert gg.is_constant()

def regular(full=False):
    Q,guards,E,N=build();W,px,clean=width_guards(Q,guards,E,N)
    e,n=px(E),px(N)
    def hm(f):return sum(W.from_dict({(j,i):v})*n**k*e**(f.degrees()[0]-k) for (k,j,i),v in f.to_dict().items())
    gu=[hm(f) for f in guards+[E]];out={}
    for k,f in Q.items():
        x=hm(f);drop=[]
        for i,g in enumerate(gu):
            while x and g:
                w=x.gcd(g)
                if w.is_constant():break
                x=x//w;drop.append((i,w.degrees(),bool(w%g)))
        assert all(i in (0,1) and not partial for i,d,partial in drop)
        print('regular',k,x.degrees(),drop,flush=True);out[k]=x
    return (out,gu,e,n) if full else out

def primitive(q):
    d=q.to_dict();L=lcm(*(int(c.denominator) for c in d.values()));p={i:int(c.numerator)*(L//int(c.denominator)) for i,c in d.items()}
    g=gcd(*p.values());return {i:c//g for i,c in p.items()}

def exact(W):
    P=flint.fmpz_mpoly_ctx.get(('b','a'));Q={k:P.from_dict(primitive(w)) for k,w in W.items()};o=[];t=monotonic()
    for k in ('P','F','N'):
        r=Q['G'].resultant(Q[k],0);rs=r.to_dict();assert all(not i for i,j in rs)
        q=flint.fmpz_poly([rs.get((0,j),0) for j in range(r.degrees()[1]+1)]);o.append(q)
        g=reduce(lambda a,b:a.gcd(b),o);print('exact projection',k,q.degree(),'gcd',g.degree(),'elapsed',round(monotonic()-t,2),flush=True)
    assert [f.degree() for f in o]==[630,1036,954]
    assert g.degree()==312
    factors=g.factor()[1];print('factors',[(f.degree(),m) for f,m in factors],flush=True)
    return [([int(c) for c in f.coeffs()],m) for f,m in factors]

P=Q=flint.fmpq_poly

def field_ops(f):
 f=f/f[f.degree()]
 ev=lambda x:x%f
 def inv(c):
  d,u,v=c.xgcd(f);assert d.degree()==0 and d[0]
  return ev(u/d[0])
 def trim(a):
  while a and not a[-1]:a.pop()
  return a
 def monic(a):
  a=trim(a[:]);
  if not a:return a
  cc=inv(a[-1]);return [ev(cc*c) for c in a]
 def div(a,m):
  a=trim(a[:]);assert m[-1]==Q([1])
  q=[Q()]*(max(0,len(a)-len(m)+1))
  while len(a)>=len(m):
   k=len(a)-len(m);q[k]=a[-1]
   for j in range(len(m)-1):a[j+k]=ev(a[j+k]-q[k]*m[j])
   a.pop();trim(a)
  return trim(q),a
 def gcd(a,b):
  a,b=monic(a),monic(b)
  while b:a,b=b,monic(div(a,b)[1])
  return a
 return f,ev,trim,div,gcd

def reconstruct(G,K):
    R,a=ring('a',QQ);T,b=ring('b',R)
    def cv(f):
        e={}
        for (i,j),c in f.to_dict().items():e.setdefault((int(j),),{})[(int(i),)]=QQ(int(c.numerator),int(c.denominator))
        return T.from_dict({j:R.from_dict(v) for j,v in e.items()})
    st=monotonic();u,v=cv(G[25]),cv(G[16]);s=u.subresultants(v)
    print('Hankel guard subresultant chain b degrees',[w.degree() for w in s],round(monotonic()-st,2),flush=True)
    ell=next(w for w in reversed(s) if w.degree()==1)
    rt=lambda f:P([flint.fmpq(int(f.get((i,),0).numerator),int(f.get((i,),0).denominator)) for i in range(f.degree()+1)]) if f else P()
    L=rt(ell[(1,)])%K;M=rt(ell[(0,)])%K
    assert L and L.gcd(K).degree()==0
    print('affine residue degrees',L.degree(),M.degree(),round(monotonic()-st,2),flush=True)
    def val(f,r=0):
        e=f.to_dict();d=f.degrees()[1];l=[P([1])];m=l[:]
        for _ in range(d):l.append((l[-1]*L)%K);m.append((-m[-1]*M)%K)
        t=P()
        for j in range(d+1):
            z=P([e.get((i,j),0) for i in range(f.degrees()[0]+1)])%K
            t=(t+((z*l[d-j])%K)*m[j])%K
        return t
    for i in (16,18,19,25):
        assert not val(G[i]);print('exact B factor through Hankel guard',i,round(monotonic()-st,2),flush=True)
    return L,M

def local(W,G,E,N,q):
 ab=flint.fmpq_mpoly_ctx.get(('a','b'));xx=lambda f:ab.from_dict({(i,j):v for (j,i),v in f.to_dict().items()})
 names=('G','F','P','N','S','T')
 for cs,m in q:
  K,ev,trim,div,gcd=field_ops(Q(cs));n=K.degree()
  if K==Q([0,1]):continue
  def cvpoly(f):
   d=f.to_dict();return trim([ev(Q([d.get((j,i),0) for i in range(f.degrees()[1]+1)])) for j in range(f.degrees()[0]+1)])
  QQ={k:cvpoly(W[k]) for k in names}
  if n!=108:
   B=gcd(cvpoly(E),cvpoly(N));assert len(B)==4 and not any(B[:2]);B=B[2:]
   for k,t in QQ.items():
    count=0
    for _ in range(3):
     y,r=div(t,B)
     if r:break
     t=y;count+=1
    QQ[k]=t;assert count==(2 if k=='G' else 3)
    print('exact guard removal',n,k,count,flush=True)
   prm=103;L,M=None,None
  else:
   Gu=[None]*26
   Gu[16],Gu[18],Gu[19],Gu[25]=[xx(G[i]) for i in (11,19,20,10)]
   L,M=reconstruct(Gu,K);prm=107
  U=flint.fmpz_mod_poly_ctx(prm);rd=lambda v:int(v.numerator)%prm*pow(int(v.denominator),-1,prm)%prm
  fp=U([rd(c) for c in K.coeffs()]);assert fp.degree()==n and fp.gcd(fp.derivative()).degree()==0
  success=False
  for f,j in fp.factor()[1]:
    Kp=flint.fq_default_ctx(modulus=f,fq_type='FQ_NMOD');R=flint.fq_default_poly_ctx(Kp);a=Kp.gen();aa=[a**i for i in range(n)]
    at=lambda f:sum((Kp(rd(v))*x for v,x in zip(f.coeffs(),aa)),Kp.zero())
    pol=lambda t:R([at(v) for v in t])
    p0={k:pol(v) for k,v in QQ.items()}
    if n==108:
     la,mu=at(L),at(M)
     if not la:continue
     b0=-mu/la;lin=R([-b0,Kp.one()]);assert all(not v%lin for v in p0.values())
     # Width-only factors removed from the five normalized constraints at the
     # Hankel fiber, plus the true affine pivot. See the structural proof.
     for i in range(10): assert pol(cvpoly(G[i]))(b0)
     assert pol(cvpoly(E))(b0)
     prs={k:v//lin for k,v in p0.items()}
    else:prs=p0
    top=[k for k,v in p0.items() if v and v.degree()==len(QQ[k])-1]
    if top and reduce(lambda a,b:a.gcd(b),prs.values()).degree()==0:
     print('degree',n,'exact local lift',prm,f.degree(),'full',top,flush=True);success=True;break
  assert success,(n,prm)



def run(fiber_only=False):
    zero()
    W,G,E,N=regular(True)
    q=literal_eval(Path(__file__).with_name('right-fixed-e-widths.txt').read_text()) if fiber_only else exact(W)
    assert sorted((len(c)-1,m) for c,m in q)==[(1,36),(6,10),(9,12),(108,1)]
    local(W,G,E,N,q)

if __name__=='__main__':
    from sys import argv
    run('--fiber-only' in argv)

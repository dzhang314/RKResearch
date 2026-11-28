"""Exact asymmetric half-at-10 physical-edge exit.

Requires Python, sympy, and python-flint. The default reconstructs both global
integer resultants exactly before auditing the width fields. --fiber-only reuses
the subagent's already computed factor checkpoint to replay the final checks.
"""
from math import gcd,lcm,factorial
from pathlib import Path
from ast import literal_eval
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
def build(augmented=True):
    R,a,b,z=ring('a,b,z',QQ);B=model(R,a,b);X=B['X']
    h,e,d,H,I0,I1,I2,C1=[B[k] for k in ('h','e','d','H','I0','I1','I2','C1')]
    E=B['A']*h+B['B'];N=-(B['C']*h+B['D'])
    hull=(X-a)*(X-h)*(X-d)*(X-e)
    ms=[integ(X*(1-X)*hull,j) for j in range(5)]
    w=[ms[j+1]-z*ms[j] for j in range(4)]
    D=w[0]*w[2]-w[1]*w[1];SN=w[0]*w[3]-w[1]*w[2];PN=w[1]*w[3]-w[2]*w[2]
    R0=d*d*D-d*SN+PN;R1=-D+SN-PN
    Rrow=[R0*u+R1*v for u,v in zip(B['dr0'],B['dr1'])]
    Cx,T=ring('t',R)
    xx=lambda f:Cx(f)
    L0=xx(a-e)*(xx(a)-T);L1=-xx(e)*T
    G=L0*xx(R0)+xx(ev(T4,a))*L1*xx(R0)+xx(ev(T4,b))*L0*xx(R1)+xx(ev([ev(r,b) for r in U4],a))*L1*xx(R1)
    s=xx(SN)-xx(D)*T  # D times the other free clock s.
    Izs=xx(D*(I2-z*I1))+s*xx(z*I0-I1)
    u0=dot(B['el'](a),Rrow);kh=B['k0']*R0+B['k1']*R1
    L=xx(a*kh)*Izs+30*xx(h*(a-h)*(h-z)*u0)*(xx(C1*D)-s*xx(H))
    K=lambda p:sum(c*z**i[0] for i,c in p.items())
    Eport=K(B['Ks'][0])*R0+K(B['Ks'][1])*R1
    g0,g1=[G.get((j,),R.zero) for j in (0,1)]
    l0,l1=[L.get((j,),R.zero) for j in (0,1)]
    assert G.degree()==L.degree()==1
    mr=g1*l0-l1*g0
    f0=D*g0*g0+SN*g1*g0+PN*g1*g1
    f1=D*l0*l0+SN*l1*l0+PN*l1*l1
    Omega=ms[0]*PN-ms[1]*SN+ms[2]*D
    assert Omega.degrees()[2]==0
    p0,q0=I2-h*I1,h*I0-I1
    us=-(z-e)*(p0+q0*z)
    vs=(z-e)*(p0*z*D+q0*z*SN-q0*PN)-Omega*z*(1-z)*(z-a)*(z-d)
    sc=g1*vs-us*D*g0
    sn=vs*vs+SN*us*vs+D*PN*us*us
    guards=B['known'][:10]+[z,z-1,z-a,z-d,z-h,z-e,D,SN*SN-4*D*PN]+[D*y*y-SN*y+PN for y in (0,1,a,d,h,e,z)]
    res={'G':Eport,'R':mr,'F':f0,'Q':f1}
    if augmented:
        res.update({'S':sc,'T':sn});guards.append(Omega)
    return res,guards,E,N

def data(augmented=True):
    Q,G,E,N=build(augmented)
    C=flint.fmpq_mpoly_ctx.get(('z','b','a'))
    cv=lambda u:C.from_dict({(j,k,i):flint.fmpq(int(v.numerator),int(v.denominator)) for (i,k,j),v in u.items()})
    gu=list(map(cv,G))
    raw={}
    for k,f in Q.items():
        f=cv(f)
        # Remove live factors in the trivariate numerators before specialization.
        factors=[]
        for i,g in enumerate(gu):
            while not f%g:
                f=f//g; factors.append(i)
        if augmented:
            assert factors=={'G':[1],'R':[0,0,0,0,1,1],'F':[0,0,1,1],
                             'Q':[0,0,0,0,0,0,1,1,16,16],'S':[0,1],'T':[]}[k]
        raw[k]=f
    return raw,gu,cv(E),cv(N)

def regular(augmented=True):
    Q,gu,E,N=data(augmented)
    C=flint.fmpq_mpoly_ctx.get(('a','b'))
    wr=lambda f:C.from_dict({(i,j):c for (_k,j,i),c in f.to_dict().items()})
    ed,nn=wr(E),wr(N)
    def tr(f):
        n=f.degrees()[0]
        return sum(C.from_dict({(i,j):v})*nn**k*ed**(n-k) for (k,j,i),v in f.to_dict().items())
    ga=[tr(f) for f in gu+[E]]
    ans={}
    for k,f in Q.items():
        d=tr(f);out=[]
        for i,g in enumerate(ga):
            if not g:continue
            while d:
                q=d.gcd(g)
                if q.is_constant():break
                d=d//q;out.append((i,q.degrees()))
        ans[k]=d
        if augmented:
            assert all(i==0 and degrees==(1,0) for i,degrees in out)
        print(k,d.degrees(),out,flush=True)
    return ans,ga

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
Q=flint.fmpq_poly

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

P=flint.fmpq_poly

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

def lift(G,L,M,K,F):
    names=('G','F','R','S','T')
    p=107;U=flint.fmpz_mod_poly_ctx(p);rd=lambda c:int(c.numerator)%p*pow(int(c.denominator),-1,p)%p
    A=U([rd(c) for c in K.coeffs()]);assert A.degree()==K.degree() and A.gcd(A.derivative()).degree()==0
    for f,_ in A.factor()[1]:
        try:
            Kp=flint.fq_default_ctx(modulus=f,fq_type='FQ_NMOD');R=flint.fq_default_poly_ctx(Kp);a=Kp.gen()
            pa=[a**j for j in range(K.degree())]
            rv=lambda q:sum((Kp(rd(c))*v for c,v in zip(q.coeffs(),pa)),Kp.zero())
            if not rv(L):continue
            b0=-rv(M)/rv(L);lin=R([-b0,Kp.one()]);print('testing mod place',f.degree(),flush=True)
            def cv(q):
                a2=[a**i for i in range(q.degrees()[0]+1)];t=[Kp.zero() for i in range(q.degrees()[1]+1)]
                for (i,j),v in q.to_dict().items():t[j]+=Kp(rd(v))*a2[i]
                return R(t)
            assert a and b0 and cv(G[26])(b0)
            raw={k:cv(F[k]) for k in names}
            assert all(not t%lin for t in raw.values())
            assert any(t.degree()==F[k].degrees()[1] for k,t in raw.items())
            assert reduce(lambda a,b:a.gcd(b),[t//lin for t in raw.values()]).degree()==0
            print('Degree-132 fiber exact forbidden factor + whole unit lift done',p,f.degree(),flush=True)
            return
        except (AssertionError,ValueError,ZeroDivisionError):pass
    raise AssertionError('no usable place')

def scan(factors):
 tm=monotonic();F,G=regular();_,_,E,N=data()
 C=flint.fmpq_mpoly_ctx.get(('a','b'));w=lambda f:C.from_dict({(i,j):c for (z,j,i),c in f.to_dict().items()})
 En,Nu=w(E),w(N);names=('G','F','R','S','T','Q')
 aa=flint.fmpz_poly([0,1]);fb=aa*(aa-1)*(aa-2)
 for cs,m in factors:
  f0=flint.fmpz_poly(cs);deg=f0.degree()
  if not fb%f0:print('forbidden',f0,m,flush=True);continue
  K,eval,trim,div,gcd=field_ops(Q(cs))
  def cv(w):
   ds=w.to_dict()
   return trim([eval(Q([ds.get((i,j),0) for i in range(w.degrees()[0]+1)])) for j in range(w.degrees()[1]+1)])
  if deg==132:
   L,M=reconstruct(G,K)
   lift(G,L,M,K,F)
   continue
  V={k:cv(F[k]) for k in names}
  print('a factor',deg,m,'specialized b degrees',[len(v)-1 for v in V.values()],flush=True)
  B=None
  if deg in (15,6):
   B=gcd(cv(En),cv(Nu));assert len(B)==2
  elif deg==4:B=[Q(),Q([1])]
  if B:
   for k,v in V.items():
    cnt=0
    while cnt<5 and v:
     d,r=div(v,B)
     if r:break
     v=d;cnt+=1
    V[k]=v
    print(' exact guard power',deg,k,cnt,flush=True)
  win=False
  for p in (103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199):
   try:
    U=flint.fmpz_mod_poly_ctx(p)
    rm=lambda c:int(c.numerator)%p*pow(int(c.denominator),-1,p)%p
    T=U([rm(c) for c in K.coeffs()])
    if T.degree()!=deg or T.gcd(T.derivative()).degree()!=0:continue
    for f,_ in T.factor()[1]:
     Kp=flint.fq_default_ctx(modulus=f,fq_type='FQ_NMOD');Bp=flint.fq_default_poly_ctx(Kp);a=Kp.gen()
     pa=[a**int(i) for i in range(deg)]
     def vv(pol):return sum((Kp(rm(c))*a0 for c,a0 in zip(pol.coeffs(),pa)),Kp.zero())
     U0={k:Bp([vv(c) for c in row]) for k,row in V.items()}
     gv=reduce(lambda a,b:a.gcd(b),U0.values());live=[k for k,g in U0.items() if g and g.degree()==len(V[k])-1]
     if (gv.degree()==0 and live):
      print(' LIFT',deg,p,f.degree(),live,round(monotonic()-tm,2),flush=True);win=True;break
     if p in (103,107,109):print(' unresolved place',deg,p,f.degree(),gv.degree(),live,flush=True)
    if win:break
   except (ValueError,ZeroDivisionError) as err:continue
  assert win,(deg,m)



def factor_widths():
    W,_=regular(False)
    Q={k:irep(v) for k,v in W.items()}
    rr=exact(Q['G'],{k:Q[k] for k in ('F','R')})
    assert [v.degree() for v in rr.values()]==[2440,2757]
    g=rr['F'].gcd(rr['R'])
    assert g.degree()==1667
    return [([int(v) for v in q.coeffs()],m) for q,m in g.factor()[1]]

def run(use_checkpoint=False):
    if use_checkpoint:
        print('Replaying final fields with an already exact external projection checkpoint.',flush=True)
        factors=literal_eval(Path(__file__).with_name('edge-h10-width-factors.txt').read_text())
    else:
        factors=factor_widths()
    assert sorted((len(cs)-1,m) for cs,m in factors)==[
        (1,5),(1,98),(1,264),(3,4),(4,4),(6,30),(8,4),(15,30),
        (50,2),(57,2),(132,3)]
    scan(factors)

if __name__=='__main__':
    from sys import argv
    run('--fiber-only' in argv[1:])

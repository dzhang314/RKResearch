"""Exact rank-zero exclusion on the mirrored variable edge with A0 live."""
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
 g0={k:Norm(f) for k,f in [('F',F),('G',G),('M',M),('S',X0)]}
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

def run():
 P,L=build()
 for k,d in [('J',8),('R',12)]:
  r=L[k];tests='FGS' if k=='J' else 'FGMS'
  w=reduce(lambda g,h:g.gcd(h),[r.resultant(P[j],0) for j in tests]);fs=w.factor()[1]
  assert len(fs)==1 and fs[0][0].degrees()==(0,d) and fs[0][1]==6
  g=fs[0][0];F=Q([g.to_dict().get((0,i),0) for i in range(d+1)]);K,ev,trim,div,gg=field_ops(F)
  def cv(f):
   aa=f.to_dict();return trim([ev(Q([aa.get((j,i),0) for i in range(f.degrees()[1]+1)])) for j in range(f.degrees()[0]+1)])
  q=cv(r)
  for name in tests:
   q=gg(q,cv(P[name]));print(k,'degree a',d,'b gcd after',name,len(q)-1,flush=True)
   if len(q)==1:break
  if len(q)>1: assert not div(cv(L['A']),q)[1]
  print('all finite residual b roots force A0=0' if len(q)>1 else 'all finite b excluded',flush=True)

if __name__=='__main__':run()

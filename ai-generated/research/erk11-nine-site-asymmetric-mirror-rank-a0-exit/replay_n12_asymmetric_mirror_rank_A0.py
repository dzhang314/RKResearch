"""Exact exclusion of the mirrored A0=0 rank-zero width branch."""
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
    R,sa,sb=ring('a,b',QQ);W=model(R,sa,sb)
    C=flint.fmpq_mpoly_ctx.get(('b','a'))
    cv=lambda f:C.from_dict({(j,i):flint.fmpq(int(c.numerator),int(c.denominator)) for (i,j),c in f.items()})
    U=ev([ev(v,sb) for v in U4],sa);Ta,Tb=ev(T4,sa),ev(T4,sb);R33=(U-Ta*Tb).exquo(sa*sb)
    assert W['B']-W['C']==-W['H']*W['J']
    assert 633719116800000*(W['A']*W['D']-W['B']*W['C'])==-sa*sa*sb*sb*W['J']*R33
    Ar,Br,Rr=map(cv,(W['A'],W['B'],R33))
    f1=Rr.resultant(Ar,0);f2=Rr.resultant(Br,0)
    g=f1.gcd(f2);assert f1.degrees()==f2.degrees()==(0,24)
    factors=g.factor()[1];assert len(factors)==1 and factors[0][0].degrees()==(0,12) and factors[0][1]==1
    F=Q([g.to_dict().get((0,i),0) for i in range(13)])
    F,red,trim,div,gg=field_ops(F)
    def bt(f):
        w=f.to_dict();return trim([red(Q([w.get((j,i),0) for i in range(f.degrees()[1]+1)])) for j in range(f.degrees()[0]+1)])
    b0=gg(gg(bt(Rr),bt(Ar)),bt(Br));assert len(b0)==2
    a=Q([0,1]);b=-b0[0]
    def exact(f):
        r=Q()
        for i in reversed(bt(cv(f))):r=red(r*b+i)
        return r
    def inv(y):
        d0,u0,_=y.xgcd(F);assert d0.degree()==0 and d0[0]
        return red(u0/d0[0])
    assert not exact(W['A']) and not exact(W['B']) and not exact(R33)
    xC,xD=exact(W['C']),exact(W['D']);assert xC
    s=red(-xD*inv(xC));h=red(a/2);d=red(Q([1])-b);e=red(Q([1])-b/2)
    zs=(Q(),Q([1]),a,h,d,e,s)
    if len({tuple(w.coeffs()) for w in zs})!=len(zs):
        print('Exact width root violates calibration/distinct site guard.',flush=True);return
    def add(x,y):
        n=max(len(x),len(y));return trim([red((x[i] if i<len(x) else Q())+(y[i] if i<len(y) else Q())) for i in range(n)])
    def mul(x,y):
        q=[Q()]*(len(x)+len(y)-1)
        for i,u in enumerate(x):
            for j,v in enumerate(y):q[i+j]=red(q[i+j]+u*v)
        return trim(q)
    z1=Q([1]);P5=[z1]
    for w in (a,h,d,e,s):P5=mul(P5,[-w,z1])
    m=[red(sum((q/((i+j+2)*(i+j+3)) for i,q in enumerate(P5)),Q())) for j in range(4)]
    D=red(m[0]*m[2]-m[1]**2)
    if not D:print('Exact residual two-site pivot zero.',flush=True);return
    S=red(m[0]*m[3]-m[1]*m[2]);P=red(m[1]*m[3]-m[2]**2)
    p=[red(P*inv(D)),red(-S*inv(D)),z1]
    TA,TB=exact(Ta),exact(Tb)
    L0=[red((a-s)*a),red(s-a)];L1=[Q(),-s]
    R0=[red(-(h-d)*d),red(h-d)];R1=[h-z1,red(z1-h)]
    r=mul(add(L0,mul([TA],L1)),add(R0,mul([TB],R1)))
    g=gg(p,r)
    print('Exact degree12 a field, linear b, live residual pivot; true t/Gram common degree',len(g)-1,flush=True)
    if len(g)>1:
      print('NORM LEFT',gg(p,add(L0,mul([TA],L1))))
      print('NORM RIGHT',gg(p,add(R0,mul([TB],R1))))
    assert len(g)==1

if __name__=='__main__':run()

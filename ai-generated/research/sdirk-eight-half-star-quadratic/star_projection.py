from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent / "sdirk-eight-half-quadratic"))
import literal_front as F
from univariate import *

def star_pencil(rear,sign,phase):
    A,b,hA,hb,hs,d,W,AA,BB,CC,DD,M=F.front_data(True)
    c,e,k,l,_=F.end(sign,rear);c=1-c;e=1-e
    a,b,ha,hb,c,e,k,l=map(Rat.k,(A,b,hA,hb,c,e,k,l))
    def value(poly,s,Y):
        return sum(Rat.k(v)*s**i*Y**j for (i,j,z),v in poly.items() if not z)
    y=s*Q(3,2)-Q(1,4) if phase==0 else Q(103,72)-s
    legs=[[-1,12,-30,20],[1,-20,90,-140,70],[-1,30,-210,560,-630,252]]
    V=lambda x:[ev(v,x) for v in legs]
    V3=[V(x) for x in (a,b,s)]
    dv=det(V3)
    ah=value(AA,s,y);bh=value(BB,s,y);hy=-ah/bh
    hstar=value(hs,s,0)
    coeffs=[cramer(V3,[h*x**j for h,x in zip((ha,hb,hstar),(a,b,s))]) for j in range(3)]
    pp=[[sum(U[i]*(legs[i][j] if j<len(legs[i]) else 0) for i in range(3))/dv for j in range(6)]
        for U in coeffs]
    lv=[ev(u,y)-hy*y**j for j,u in enumerate(pp)]
    aff=(-lv[2]/lv[1],-lv[0]/lv[1])
    qs=[[zero,aff[0],one],[one,aff[1],zero]]
    ps=[[u*aff[0]+v for u,v in zip(pp[1],pp[2])],
        [u+v*aff[1] for u,v in zip(pp[0],pp[1])]]
    evpc=[ev(u,c) for u in ps];evpd=[ev(u,e) for u in ps]
    evqc=[ev(u,c) for u in qs];evqd=[ev(u,e) for u in qs]
    rearEq=[l*a-k*b for a,b in zip(mul(evqd,evpc),mul(evqc,evpd))]
    assert len(rearEq)==3

    R=Ring2(rearEq[0]/rearEq[2],rearEq[1]/rearEq[2]);beta=R.gen()
    q=[R(u)+beta*v for u,v in zip(*qs)];p=[R(u)+beta*v for u,v in zip(*ps)]


    rho=ev(p,Ring2(q[0],q[1]).gen()).norm()
    early=[s-a,s-b,y-a,y-b,y-s,value(d,s,y)]
    base=[bh,dv,lv[1],rearEq[2]]
    return (a,b,s,y,c,e),q,p,R,rho,early+base


from functools import reduce

def evalnorm(x):
  while isinstance(x,Ext):x=x.norm()
  return x
def normP(z):
  a=evalnorm(z)
  n=a.a*a.a-a.b*a.b/2
  return n
def denomP(z):
  if isinstance(z,Ext):return denomP(z.a)*denomP(z.b)
  if isinstance(z,Rat):return z.d
  return P(1)
def sf(P0):
  assert P0
  return P0//P0.gcd(P0.derivative())
def stripq(D,g):
  while D.degree()>0:
    R=D.gcd(g)
    if R.degree()==0:return D
    D=D//R
  return D
def gcds(L):
  return __import__('functools').reduce(lambda a,b:a.gcd(b),L)
def padx(v,n):return v+[0]*(n-len(v))
def moments(pegs,q,p):
  qq=mul(q,q)
  qp=mul(q,p);pp=mul(p,p)
  qr=[divmod_monic(f,qq) for f in (qp,[0]+qp,pp,[0]+pp)]
  I=lambda f:sum(x*Q(1,j+1) for j,x in enumerate(f))
  N=[padx(v,4) for u,v in qr]
  def xrem(poly):return divmod_monic(poly,q)[1]
  def plus(data,row,sc):return [v+sc*w for v,w in zip(data,row)]
  U=Ring2(q[0],q[1]);h=U.gen();px=ev(p,h)
  pxinv=px.inv()
  v0=[pxinv.a,pxinv.b];v2=xrem(mul(v0,v0))
  ci=[I(u) for u,v in qr]
  P6=[1]
  for u in pegs:P6=mul(P6,[-u,1])
  T=[]
  for j in range(6):
    f,w=divmod_monic([0]*j+P6,qq)
    r=padx(xrem(mul(v2,xrem(w))),2)
    vec=plus(plus(padx(w,4),N[2],-r[0]),N[3],-r[1])
    d0,z=divmod_monic(vec,q);assert not z
    k=padx(xrem(mul(v0,d0)),2)
    ch=k+r
    assert all(wi==sum(ch[j0]*N[j0][i] for j0 in range(4)) for i,wi in enumerate(padx(w,4)))
    T.append(I(f)-sum(v*w for v,w in zip(ch,ci)))
  xx=[det([[T[i+j+k] for j in range(3)] for i in range(3)]) for k in range(2)]
  xx.append(det([[T[i+j] for j in (0,1,3)] for i in range(3)]))
  return T,xx

def project(model):
    pegs,q,p,R,rho,guards=model
    base=sf(reduce(lambda a,b:a*b,[normP(g)*denomP(g) for g in guards]))
    singular=normP(rho)
    singular_den=denomP(rho)
    support=base*singular*singular_den
    assert support
    # Every coefficient needed on the open chart is regular off this support.
    for u in pegs+tuple(q)+tuple(p)+(R.c0,R.c1,rho):
        assert stripq(denomP(u),support).degree()==0
    T,G=moments(pegs,q,p)
    N=[evalnorm(g) for g in G]
    N.append(evalnorm(G[0].a*G[1].b-G[0].b*G[1].a))
    for g in N:
        assert stripq(denomP(g),support).degree()==0
    D=gcds([normP(g) for g in N])
    assert D and stripq(sf(D),support).degree()==0
    S=[]
    for f in (base,sf(singular),sf(singular_den)):
        unit,fac=f.factor()
        rebound=P(unit)
        for p0,e in fac:
            rebound*=p0**e
            v=p0/p0.leading_coefficient()
            if v not in S:S.append(v)
        assert f==rebound
    print("Univariate projection degrees", sf(D).degree(), [u.degree() for u in S],flush=True)
    return S

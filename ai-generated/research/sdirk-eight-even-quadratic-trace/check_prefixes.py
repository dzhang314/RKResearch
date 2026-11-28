#!/usr/bin/env python3
"""Construct or reject the exact prime-field symmetric quadratic candidates."""
from math import prod
from flint import nmod_poly
from controls import CONTROLS
from prime_certificates import certify

def analyze(p,ph,q,g,u,a,clock4,d1,d2):
  assert certify(p)
  seen=[]
  cast=lambda x:x%p
  inv=lambda x:pow(x%p,-1,p)
  div=lambda x,d:cast(x*inv(d))
  V=lambda xs:list(map(cast,xs))
  one=[1]*10;zero=[0]*10
  dot=lambda a,b:cast(sum(x*y for x,y in zip(a,b)))
  had=lambda a,b:V(x*y for x,y in zip(a,b))
  r0=((2*g-1)**2+q)%p
  r=lambda x:cast((2*x-1)**2+q)
  G=lambda x:div(g*g*r(x),2*r0)
  m0=(q+inv(3))%p;m2=(div(q,3)+inv(5))%p;m4=(div(q,5)+inv(7))%p
  w=div(m4,m2)
  b=cast(1-a);h=inv(2)
  assert (2*a-1)**2%p==w and a not in (b,h)
  ze=[a,h,b]
  head=[g,cast(g*(1+u)),cast(g*(1+2*u))]
  tail=[cast(1-x) for x in reversed(head)]
  mu=div(m2,2*w*(w+q))
  muh=div(m0-div(m2,w),q)
  ZW={a:mu,b:mu,h:muh}
  assert mu and muh

  # A live fourth row uses the full genuine grade-three principal relation.
  def fourth():
    X=nmod_poly([0,1],p)
    gg=g*g*inv(2)%p
    K=[gg,G(head[1]),G(head[2]) if ph=='A' else 0]
    P=nmod_poly([],p)
    for i,xi in enumerate(head):
       oth=[x for j,x in enumerate(head) if i!=j]
       term=prod((X-s for s in oth),start=nmod_poly([1],p))
       P+=term*div(K[i],prod(xi-t for t in oth))
    J=nmod_poly([0]+[div(int(P[j]),j+1) for j in range(3)],p)
    w1=div(int(J(head[0])),K[0]);w2=div(int(J(head[1])),K[1])
    Q1=div(w2-w1,head[1]-head[0]);Q0=cast(w1-Q1*head[0])
    Pgraph=( (2*X-1)**2+q)*div(gg,r0)
    base=J-g*P
    graph=base+Pgraph*(g-Q0-Q1*X)
    assert graph.degree()==3 and all(graph(x)==0 for i,x in enumerate(head) if K[i]!=0)
    assert len(graph.roots())==3 and all(e==1 for x,e in graph.roots())
    rr=[int(x) for x,e in graph.roots() if int(x) not in head and r(int(x))!=0]
    zz=[x for x in ze if base(x)==0 and (ph!='Z' or x==h)]
    return rr,zz
  fourths=fourth()
  print(p,'phase',ph,'fourth off/on',fourths,flush=True)
  modes=[]
  if ph=='A':
    assert fourths==([],[a]) and a==clock4
    for is_off in (False,True):
      mids=[(None if is_off else h,is_off),(h if is_off else None,not is_off)]
      modes.append([(x,True) for x in head]+[(a,False)]+mids+[(b,False)]+[(x,True) for x in tail])
  else:
    assert a==head[-1]
    rr,zz=fourths
    assert zz==[] and rr==[clock4]
    for x in rr:
      for y in rr:
        for is_off in (False,True):
          c5=[(None,is_off),(h,not is_off)] if is_off else [(h,False),(None,True)]
          f=[(head[0],True),(head[1],True),(a,False),(x,True)]
          t=[(cast(1-y),True),(b,False),(tail[1],True),(tail[2],True)]
          modes.append(f+c5+t)
  def residual(j):return cast(inv(j+1)-sum(w*x**j for x,w in ZW.items()))
  idx=[(i,j) for i in range(10) for j in range(i)]
  def elimination(lins,n,onlyker=False):
    S={}
    for j,line in enumerate(lins):
      row=V(line)
      for i in range(n):
        if (c:=row[i])!=0:
          if i in S:row=V(x-c*y for x,y in zip(row,S[i]))
          else:S[i]=V(x*inv(c) for x in row);break
      else:
        if any(row[n:]):return None,len(S),j
    if not onlyker:
      v=[0]*n
      for i in sorted(S,reverse=True):
        row=S[i];v[i]=cast(row[n]-dot(v,row[:n]))
      return v,len(S),None
    out=[]
    for j in range(n):
      if j in S:continue
      v=[int(j==k) for k in range(n)]
      for i in sorted(S,reverse=True):v[i]=-dot(v,S[i])%p
      out.append(v)
    return out
  for raw in modes:
    off=[x for x,h in raw if h and x is not None]
    if len(set(off))!=6:continue
    # All six fixed exterior/off-zero clocks force the seventh by precision 7.
    X=nmod_poly([0,1],p)
    K=prod((X-x for x in off),start=nmod_poly([1],p))
    M0=sum(int(K[j])*residual(j) for j in range(7))%p
    M1=sum(int(K[j])*residual(j+1) for j in range(7))%p
    if M0==0:continue
    xstar=div(M1,M0)
    c=[x if x is not None else xstar for x,h in raw]
    gl=[G(x) if h else 0 for x,(_,h) in zip(c,raw)]
    off=[i for i,h in enumerate(gl) if h!=0]
    if len(off)!=7 or len({c[i] for i in off})!=7:continue
    cp=[V(x**j for x in c) for j in range(8)]
    wp,rank,bad=elimination([[cp[j][i] for i in off]+[residual(j)] for j in range(7)],7)
    assert rank==7 and bad is None
    b=[0 if h else ZW[x] for x,(_,h) in zip(c,raw)]
    for j,w in zip(off,wp):b[j]=w
    assert all(b)
    assert all(dot(b,cp[j])==inv(j+1) for j in range(8))
    assert all(dot(b,had(cp[j],gl))==0 for j in range(6))
    E2=[one,c,cp[2],gl];E3=[one,c,cp[2],cp[3],gl,had(c,gl)]
    Pi,rk,bd=elimination([[v[i] for v in E2]+[cp[3][i]] for i in range(4)],4)
    assert Pi is not None and rk==4 and bd is None
    profile=lambda i:dot(Pi,[f[i] for f in E2])
    assert all(profile(i)==c[i]**3%p for i in range(4))
    cuts=elimination([[v[i] for v in E3] for i in range(5,10)],6,True)
    assert cuts
    moments=[]
    for v in cuts:
      const,lin,quad,rho=Pi
      a0=div(g**3-div(c[0]**3,3),gl[0])
      a1=div((c[1]-g)*g*g+g*c[1]**2-div(c[1]**3,3),gl[1])
      av=div(a1-a0,c[1]-c[0]);au=cast(a0-av*c[0])
      b0=g
      b1=div((c[1]-g)*gl[0]+g*gl[1],gl[1])
      bv=div(b1-b0,c[1]-c[0]);bu=cast(b0-bv*c[0])
      reads=[]
      for i in range(5):
        x,h=c[i],gl[i]
        reads.append(cast(const*x+lin*(div(x*x,2)+h)+quad*(div(x**3,3)+h*(au+av*x))+rho*h*(bu+bv*x)+g*(x**3-profile(i))))
      lhs=sum(b[i]*reads[i]*dot(v,[f[i] for f in E3]) for i in range(5))%p
      rhs=sum(div(coef,4*(5+i)) for i,coef in enumerate(v[:4]))%p
      moments.append(cast(lhs-rhs))
    print('  prefix protected A(c^3) defects',moments,flush=True)
    assert len(moments)==1 and moments[0]
    seen.extend(moments)
  assert seen==[d1,d2]

for t in CONTROLS:analyze(*t)

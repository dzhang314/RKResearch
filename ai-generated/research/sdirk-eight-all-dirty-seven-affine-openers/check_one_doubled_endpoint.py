"""Affine seven-clock case: first and second forward labels S, terminal D."""
from reconstruct_one_end import *
from sympy.polys.agca.extensions import MonogenicFiniteExtension
from itertools import permutations

def k(v):return 1+2*v-v*v
def hub(v):return -2+v+4*v*v-v**3
def qnum(v):return (1+4*v-4*v*v)*hub(v)+4*v*v*(3*v-2)

def qread(E,v,mode):
  if not v or not k(v):return None
  if mode=='A':
    if 3*v==E(2):return None
    assert hub(v)
    r=qnum(v)/hub(v)
  else:
    if v in (E.one,E(2)):return None
    r=k(v)
  return r/2 if r else None

def check_all():
 for mf,E,a0,b0,d0,z0,xf0,yf0,ye0 in rec():
  B0,W=ring('V',E)
  o=E.one
  xzero=o-a0
  x2=3-o/a0
  xf=xf0
  ue=x2-1
  gf=qread(E,ue,mf)
  assert gf
  R=lambda x:(x-o+a0)/(2*a0)
  assert R(x2)==k(ue)/2 and gf!=R(xf)
  epoint=d0-1
  L=lambda x:L4(2*x-d0,d0)/560
  assert R(xzero)==E.zero and L(xzero)
  # Singleton second and third at the reverse second and third forces arithmetic:
  # star would have equal nonzero residuals at different S clocks.
  H=lambda x:(x-o)*(x-x2)*(x-(d0-1-W))*(x-(d0-1-2*W))
  h_s=H(xzero)-L(xzero)
  aphase=qnum(W)*(b0+W)-k(W)*hub(W)*(b0+2*W)
  gc=aphase.gcd(h_s)
  print('S/S reverse',mf,E.mod.degree(),gc.degree(),flush=True)
  assert gc.degree()==0
  # Complete splitting of the three D labels. No real-root selection.
  numP=L3(W,d0)*L4(z0,d0)-L4(W,d0)*L3(z0,d0)
  PP=numP.exquo(W-z0).monic()
  assert PP.degree()==3 and not PP.evaluate(W,ye0) and not PP.evaluate(W,yf0)
  mono2=PP.exquo(W-ye0)
  if yf0==ye0:
    P2=S.Poly.from_dict(mono2.to_dict(),S.Symbol('v'),domain=E)
    assert P2.is_irreducible and P2.degree()==2
    F=MonogenicFiniteExtension(P2)
    emb=lambda t:F.convert(t,E)
    y2=F.generator
    y3=-emb(mono2[(1,)])-y2
    doubled=[emb(ye0),y2,y3]
    degree=2*E.mod.degree()
  else:
    F=E
    emb=lambda t:t
    doubled=[ye0,yf0,-PP[(2,)]-ye0-yf0]
    degree=E.mod.degree()
  aa,bb,d,z,xf,ye,gf,x2=(emb(x) for x in (a0,b0,d0,z0,xf0,ye0,gf,x2))
  one=F.one
  doubles=[(d+y)/2 for y in doubled]
  assert all(doubles[i]!=doubles[j] for i in range(3) for j in range(i+1,3))
  assert all(L3(2*x-d,d)*L4(z,d)-L4(2*x-d,d)*L3(z,d)==F.zero for x in doubles)
  assert all(x not in doubles for x in (one,x2))
  assert doubles[0]==d-1
  L=lambda x:L4(2*x-d,d)/560
  R=lambda x:(x-one+aa)/(2*aa)
  known_s=[(one,L(one)/R(one)),(x2,L(x2)/R(x2))]
  oldD=[v for v in doubles if v!=d-1]
  def contain(xs,x):
    return any(x==q for q in xs)
  def verify_fit(xnew_s,gRev,revD):
    if contain(doubles,xnew_s) or contain((one,x2),xnew_s) or not R(xnew_s):return 'guard'
    lam=R(xnew_s)/gRev
    assert lam
    vals=known_s+[(xnew_s,L(xnew_s)/R(xnew_s))]
    def C(y):
      ret=F.zero
      for j,(x,v) in enumerate(vals):
        for i,(z,u) in enumerate(vals):
           if i!=j:v=v*(y-z)/(x-z)
        ret+=v
      return ret
    assert all(C(x)==v for x,v in vals)
    B=(L(xf)-gf*C(xf))/(gf*(gf-R(xf)))
    if not B: return 'guard'
    def good(x,gh):
      return gh!=R(x) and not (L(x)-gh*C(x)-B*gh*(gh-R(x)))
    candidates=[(x,lam*g) for x,g in revD]
    if any(x==xf and g==gf for x,g in candidates):return 'guard'
    return 'survive' if all(good(x,g) for x,g in candidates) else 'excluded'
  result=[]
  for x,y in permutations(oldD,2):
    xR,yR=d-x,d-y
    u=xR-one
    for m in ('A','S'):
      xx=1+2*u if m=='A' else 3-u
      if yR==xx and qread(F,u,m):
         result.append(('D,D','survive'))
  for x in oldD:
    xR=d-x
    for phase in ('A','S'):
      # Reverse D,S (second double, third singleton).
      v=xR-one
      read=qread(F,v,phase)
      if read:
        yR=1+2*v if phase=='A' else 3-v
        result.append(('D,S',verify_fit(d-yR,read,[(d-1,one/2),(x,k(v)/2)])))
      # Reverse S,D (third double, second singleton).
      v=(xR-1)/2 if phase=='A' else 3-xR
      read=qread(F,v,phase)
      if read:
        result.append(('S,D',verify_fit(d-1-v,k(v)/2,[(d-1,one/2),(x,read)])))
  print(mf,'degree',degree,'reverse D-read fits',result,flush=True)
  assert len(result)==8 and all(r=='excluded' for t,r in result)
 print('verified the one-doubled-endpoint affine graph when the second label at the singleton end is singleton')

if __name__=='__main__':
 check_all()

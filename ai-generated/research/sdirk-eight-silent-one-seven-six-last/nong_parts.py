from nong_front import *
from remove_h4 import mark_h4

def lc_s(F,i):
 return coeff1(sum((expr(v)*g**k for (a,b,k),v in parts(F).items() if not a and b==i),Dctx.constant(0)),2)

def rroot(F,which):
 return coeff1(sr(F,which),2)

@lru_cache(None)
def pieces(f,slot,br):
 G=candidates(f,slot,br)
 Phi,E0,E1,T0,T1,*_=core(f,slot)
 cv=lambda a:B0(Epoly(JJ(a))) if a else B0(0)
 A,B,_=map(cv,ends(f,1));L=A if slot==0 else B
 flags=[]
 if br==4:
  F1=sr(sr(E0,1),0);F2=sr(sr(E1,1),0)
  flags.append(('r',gcdp(coeff1(F1,2),coeff1(F2,2))))
 else:
  flags.append(('r',coeff1(sr(Phi,1),2)))
  flags.append(('a',coeff1(sum((expr(v*L**j)*g**k for (i,j,k),v in parts(Phi).items() if not i),Dctx.constant(0)),2)))
  flags.append(('lead',lc_s(Phi,2)))
 Z=[(G,frozenset())]
 for key,F in flags:
  if len(F)<=1:continue
  Y=[]
  for X,bs in Z:
   Q=gcdp(X,F);R=guarded(X,[F])
   if len(Q)>1:Y.append((mon(Q),bs|{key}))
   if len(R)>1:Y.append((mon(R),bs))
  Z=Y
 print('exact padded/leading components',f,slot,br,[(len(Y)-1,set(w)) for Y,w in Z],flush=True)
 return mark_h4(f,slot,br,Z)

def modparts(f,slot,br,p,t):
 Z=pieces(f,slot,br)
 for r0,_ in nmod_poly(list(Lco),p).roots():
  V=Bfield(nmod_poly([-int(r0),1],p),p,t)
  cv=lambda e:int(V(e).x[0])
  for Y,bs,h4ok in Z:
   Mp=nmod_poly(list(map(cv,Y)),p)
   assert Mp.degree()==len(Y)-1 and Mp.leading_coefficient()==1
   for G,_ in Mp.factor()[1]:
    W=Bfield(G,p,t);g=W(nmod_poly([0,1],p));r=W(int(r0))
    cast=lambda v:W(cv(v))
    h0=None if h4ok is None else [ev(list(map(cast,v)),g) for v in h4ok]
    yield W,g,r,cast,bs,h0

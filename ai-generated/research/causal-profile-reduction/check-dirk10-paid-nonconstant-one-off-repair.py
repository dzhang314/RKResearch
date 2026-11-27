from itertools import permutations
import sys
p=int(sys.argv[1]) if len(sys.argv)>1 else 419

def d(a,b):
 if not b%p: raise ZeroDivisionError
 return a*pow(b%p,-1,p)%p

def integral(cs,z):return sum(d(a*z**(i+1),i+1) for i,a in enumerate(cs))%p

def nodal(xs):
 cs=[1]
 for x in xs:cs=[((cs[i-1] if i else 0)-x*(cs[i] if i<len(cs) else 0))%p for i in range(len(cs)+1)]
 return cs

def card_tap(xs,k,z):
 rest=[x for x in xs if x!=k]; den=1
 for x in rest: den=den*(k-x)%p
 assert len(rest)==len(xs)-1
 return d(integral(nodal(rest),z),den)

def H(x):return (42*x**5-84*x**4+56*x**3-14*x**2+x)%p

def coeffF(t):
 h=[0,1,-14,56,-84,42];F=[0]*5;F[4]=h[-1]
 for j in range(3,-1,-1):F[j]=(h[j+1]+t*F[j+1])%p
 assert (h[0]+t*F[0])%p==0
 return F

I=tuple(x for x in range(p) if (42*x**4-84*x**3+56*x*x-14*x+1)%p==0)
assert len(I)==4
fixed=(0,*I,1)
betaPrime={t:integral(nodal([s for s in fixed if s!=t]),1) for t in I}
infos={};bad=[];sol=[]; late=[]; equal=[]; collision=[]; three=[]; factors=[]
for U,W,R,X in permutations(I):
 x=(1-X)%p
 try:
  K={U:d(-U**3,6),W:d(W**3*(2*U-W),6*(U-2*W)),R:d(R**3*(2*U-W)*(3*R*R-5*R*(U+W)+10*U*W),6*(4*R*U*U-13*R*U*W+4*R*W*W+U*U*W+U*W*W))}
  L=d(10*R*U*U-25*R*U*W+10*R*W*W+U*U*W+U*W*W,6*(U-W)**2)
 except ZeroDivisionError: bad.append(('tail',U,W,R,X));continue
 E={t:K[t]*betaPrime[t]%p for t in K}
 if not all(E.values()):bad.append(('E',U,W,R,X));continue
 for tauR in (*I,1):
  tau=(1-tauR)%p
  s,t,*rest=[j for j in (U,W,R) if j!=tauR]
  if E[s]==E[t]: equal.append((U,W,R,X,tauR,s,t)); continue
  qR=d(E[s]*s-E[t]*t,E[s]-E[t]);q=(1-qR)%p
  if rest:
   assert len(rest)==1
   z,=rest
   if (E[z]*(z-qR)-E[s]*(s-qR))%p: continue
   three.append((U,W,R,X,tauR,qR))
  if q in fixed:collision.append((U,W,R,X,tauR,qR));continue
  if L in (qR,tauR,0):late.append((U,W,R,X,tauR,qR,L))
  infos[U,W,R,X,tauR]=(qR,L)
  if tau==0 or tau==x:continue
  for qc in [True,False]:
   xi,a=(q,tau) if qc else (tau,q)
   if xi == (1-U)%p:continue
   nodes=(0,xi,a,1,x)
   if len(set(nodes))<5:bad.append(('collision',U,W,R,X,tauR,qR));continue
   S={j:card_tap(nodes,j,x) for j in nodes}
   if not all(S.values()):bad.append(('taps',U,W,R,X,tauR,qR,[j for j,v in S.items() if not v]));continue
   if qc:
    f=coeffF(tau); sa=(d(integral(f,x),S[a])-sum(c*a**i for i,c in enumerate(f)))%p
   else:sa=d(-H(q),q-tau)
   vals={1:d(-1,1-tau),a:sa}
   if not all(vals.values()):bad.append(('scaled',qc,U,W,R,X,tauR,qR,vals));continue
   for y,z in ((1,a),(a,1)):
    hy=d(xi**2*y**3,36*(y-xi)); gamma=d(xi**3,6); alpha=d(3*(y-xi)*(y-2*xi),xi*xi)
    term=gamma*(y-d(xi,2))*vals[y]
    bef=alpha*H(xi)*hy-term*(xi-tau) if qc else alpha*hy*(S[y]*vals[y]+S[z]*vals[z])-term*S[xi]
    aft=36*(xi-y)*(y-2*z)*vals[z]*hy-xi**2*z**3*(2*y-z)*vals[y]
    if not bef%p or not aft%p:sol.append((qc,U,W,R,X,tauR,qR,y,bef%p,aft%p))
print('p',p,'I',I,'bad',len(bad),'equal eliminated',len(equal),'collisions',len(collision),'late',len(late),'three supp',len(three),'early fail',len(sol),'infs',len(infos));
for name,res in [('bad',bad),('coll',collision),('late',late),('three',three),('sol',sol)]:print(name,res[:20])
assert not (bad or equal or collision or late or three or sol)
assert len(infos)==72

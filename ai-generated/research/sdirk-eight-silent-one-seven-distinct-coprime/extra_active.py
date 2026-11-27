"""Three active tails with a separate reverse aggregate: exact nodal projection."""
from no_extra import *

def invpoly(F,a,M):
 a=list(a); M=list(M)
 r0,r1=M,a;v0,v1=[],[F(1)]
 while r1:
  q,r=divp(r0,r1)
  r0,r1=r1,r
  v0,v1=v1,add(v0,sc(mul(q,v1),-1))
 assert len(r0)==1
 z=sc(v0,r0[0].inv())
 return qr(z,M)[1]

@lru_cache(None)
def bezout():
 F=F2
 L=list(map(F,Lco));M=mon(L)
 WL=[sum(L[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
 W=invpoly(F,WL,M)
 assert qr(mul(W,WL),M)[1]==[F(1)]
 return [qr([F(0)]*j+W,M)[1] for j in range(3)]

def newton(n,deg):
 H=[cx.constant(1)]+[cx.constant(0)]*deg
 out=[]
 for v in n:
  H=list(H)
  for j in range(1,deg+1):H[j]=can(H[j]+v*H[j-1])
  out.append(list(H))
 return out

def poly_det(A):
 n=len(A)
 @lru_cache(None)
 def it(i,bits):
  if i==n:return cx.constant(1)
  ans=cx.constant(0);sg=1
  for j in range(n):
   if bits&(1<<j):
    if A[i][j]:ans+=sg*can(A[i][j]*it(i+1,bits^(1<<j)))
    sg=-sg
  return can(ans)
 return it(0,(1<<n)-1)

@lru_cache(None)
def polys(front,rear):
 A,B,m,ha,hb,H4,qA,qB,q0,q1,*_=phases(front)
 q,b=term(q0,g)*g,term(q1,g)
 pA,pB=g*expr(A),g*expr(B)
 x=1-g;c=x-g*u;d=x-g*(2-u if rear else 2*u)
 k=1+2*u-u*u
 K=[pA,pB,x,c,d]
 L4=lambda v:sum(w*v**i for i,w in enumerate(Lco))
 QQ=lambda v:q+b*v
 Hn=newton(K,7)
 Cs=[can(q*q),can(2*q*b),can(b*b)]
 V=bezout()
 C=[can(sum(Cs[i]*(expr(V[i][j]) if j<len(V[i]) else 0) for i in range(3))) for j in range(4)]
 arr=[]
 for i in range(5):
  row=[can(sum(Lco[s]*Hn[i][s+j-i] for s in range(5) if s+j>=i)) for j in range(4)]
  row.append(can(sum(C[j]*Hn[i][j-i] for j in range(i,4))))
  arr.append(row)
 MM=poly_det(arr)
 assert MM
 P,Q,R,S,T=L4(x),L4(c),L4(d),QQ(c),QQ(d)
 D=QQ(x)
 if rear:
  F=can((2-u)*Q*T*D-u*R*S*D+k*(2*u-2)*P*S*T)
  for a in (0,1,2):F=exdiv(F,u-a)
 else:
  H=-2+u+4*u*u-u**3;J=4*u**3-12*u*u+3*u+2
  F=exdiv(exdiv(can(H*R*S*D+2*J*Q*T*D-k*J*P*S*T),u),u)
 print('active separate-aggregate polys',front,rear,'tail',F.degrees(),'nodal',MM.degrees(),flush=True)
 return F,MM,(K,P,Q,R,D,S,T,q,b)

def centered(P):
 H=can(sum(expr(v)*(1+u)**j*g**k for (i,j,k),v in parts(P).items() if v))
 assert all((not i and j%2==0) for (i,j,k),w in parts(H).items() if w)
 return can(sum(expr(v)*u**(j//2)*g**k for (i,j,k),v in parts(H).items() if v))

def exact_uc(M):
 X={}
 for (i,j,k),v in parts(M).items():
  if v:
   assert not i
   X.setdefault(j,{})[k]=v
 Y=[]
 for j in range(max(X,default=-1)+1):
  d=X.get(j,{})
  Y.append([d.get(i,F2(0)) for i in range(max(d,default=-1)+1)])
 return Y
def physical_guard(front):
 U=F2
 A,B,m,ha,hb,H4,qA,qB,q0,q1,*_=phases(front)
 x=[U(1),U(-1)];P=list(map(U,Lco))
 q=mul([U(0),U(1)],q0)
 R=sum_poly([sc(mul(power(sc(q,-1),i),power(q1,4-i)),v) for i,v in enumerate(P)])
 return [[U(0),U(1)],qA,qB,q1,R,subst(P,x),add(q,mul(x,q1)),
         [U(1),-1-A],[U(1),-1-B]]

@lru_cache(None)
def star_projection(front):
 F,MM,info=polys(front,True)
 K,P,Q,R,D,S,T,q,b=info
 A,B=exact_uc(centered(F));N=exact_uc(centered(MM))
 print('star center powers',front,len(N)-1,'common',len(gcdp(A,B))-1,flush=True)
 guard=physical_guard(front)
 # Removing a common factor from the tail equation is allowed only after proving it cannot vanish.
 J=gcdp(A,B);J=guarded(J,guard)
 x=mon(J)
 def at(v):
  Y=exact_uc(centered(v))
  n=len(Y)-1
  return sum_poly([mul(mul(power(sc(A,-1),i),power(B,n-i)),w) for i,w in enumerate(Y)])
 G=at(MM)
 X=[B,*guard,A,add(A,B),add(A,sc(B,2)),at(Q*R),at(S*T)]
 for v in K[:2]:X.append(at((K[-1]-v)*(K[-2]-v)))
 G=mon(guarded(G,X))
 print('star exact projection degree',front,len(G)-1,'exception',len(x)-1,flush=True)
 return G,A,B,x,MM

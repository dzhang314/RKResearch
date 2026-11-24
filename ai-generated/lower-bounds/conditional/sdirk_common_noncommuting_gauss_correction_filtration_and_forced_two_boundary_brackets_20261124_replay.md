# Common correction/forced bracket replay

Standalone Python, SymPy and NumPy. Exact small fixtures; the larger midpoint-extrapolation fixture matrices are constructed over the rationals then operated on modulo the displayed good prime for independent diagnostics. This is not a finite-field search for arbitrary tableaux. Executed successfully (exit 0).

```python
from fractions import Fraction as F
from math import prod
import sympy as S
import numpy as np
Q=S.Rational
def shadows(m):
 t=S.symbols('t')
 H=S.Matrix(m,m,lambda i,j:Q(1,i+j+1))
 # T_J, T_x on the scalar power basis; orthogonal projection of the new top monomial
 v=H.inv()*S.Matrix([Q(1,m+i+1) for i in range(m)])
 Tx=S.zeros(m); Tj=S.zeros(m)
 for j in range(m):
  w=S.eye(m)[:,j+1] if j+1<m else v
  Tx[:,j]=w; Tj[:,j]=w/(j+1)
 assert H*Tj+Tj.T*H==H[:,0]*H[0,:] and H*Tx==Tx.T*H
 return H,Tx,Tj
def rational_small():
 # Extrapolated midpoint, order four with 3 stages, rational varying diagonals.
 A=S.Matrix([[Q(1,2),0,0],[0,Q(1,4),0],[0,Q(1,2),Q(1,4)]])
 b=S.Matrix([[-Q(1,3),Q(2,3),Q(2,3)]])
 e=S.ones(3,1);c=A*e; C=S.diag(*c); B=S.diag(*b)
 X=e.row_join(c); H,Tx,Tj=shadows(2);Y=H.inv()*X.T*B
 R=C*A-A*C-A*A
 P=R.inv()*(S.eye(3)-X*Y); K=R.inv()*(A-X*Tj*Y); L=R.inv()*(C-X*Tx*Y)
 T=R.inv()*B.inv()*(B*A+A.T*B-b.T*b)
 assert Y*X==S.eye(2) and B*R*K+(B*R*K).T==B*A+A.T*B-b.T*b
 for u,d in [(P,2),(K,1),(L,1),(T,1)]:
  for v,d1 in [(P,2),(K,1),(L,1),(T,1)]:
   for w,d2 in [(P,2),(K,1),(L,1),(T,1)]:
    assert u*v*w==S.zeros(3)
   if d+d1>2: assert u*v==S.zeros(3)
 assert L*K!=K*L or any(u*v!=v*u for u in (P,K,L,T) for v in (P,K,L,T))
 # Small genuine strict p=3/s=2. Algebraic gamma, both signs of the square-root covered.
 gg=S.symbols('g'); pol=6*gg**2-6*gg+1
 def red(x):
  a,b=S.together(x).as_numer_denom()
  return S.rem(S.rem(a,pol,gg)*S.invert(b,pol,gg),pol,gg).expand()
 A=S.Matrix([[gg,0],[1-2*gg,gg]]);b=S.Matrix([[Q(1,2),Q(1,2)]])
 c=A*S.ones(2,1);C=S.diag(*c);B=S.diag(*b)
 X=S.ones(2,1).row_join(c);Y=H.inv()*X.T*B;R=(C*A-A*C-A*A).applyfunc(red)
 vals=[(R.inv()*V).applyfunc(red) for V in [S.eye(2)-X*Y,A-X*Tj*Y,C-X*Tx*Y]]
 for u in vals:
  for v in vals: assert (u*v).applyfunc(red)==S.zeros(2)
 # A genuine one-ghost order-four tied equality. No B inversion or assumption on bR.
 u,v=gg,1-gg;M=Q(1,2);a32=(v-Q(1,4))/(2*M)
 A=S.Matrix([[v,0,0],[u-Q(1,4),Q(1,4),0],[v-u-a32,a32,u]])
 b=S.Matrix([[0,M,M]]);c=A*S.ones(3,1);C=S.diag(*c);B=S.diag(*b)
 X=S.ones(3,1).row_join(c);Y=H.inv()*X.T*B;R=(C*A-A*C-A*A).applyfunc(red)
 vals=[(R.inv()*V).applyfunc(red) for V in [S.eye(3)-X*Y,A-X*Tj*Y,C-X*Tx*Y]]
 for i,a in enumerate(vals):
  for j,b1 in enumerate(vals):
   u=(a*b1).applyfunc(red)
   if i==0 or j==0: assert u==S.zeros(3)
   for v in vals: assert (u*v).applyfunc(red)==S.zeros(3)
 assert (B*R*vals[1]+(B*R*vals[1]).T-B*A-A.T*B+b.T*b).applyfunc(red)==S.zeros(3)
 print('exact small rational, strict algebraic, and one-ghost algebraic fixtures passed')
def noncommuting_control():
 U=S.Matrix([[0,1,0],[0,0,1],[0,0,0]])
 V=S.Matrix([[0,0,0],[1,0,0],[0,-1,0]])
 u,v,t=S.symbols('u v t')
 assert (u*U+v*V).charpoly(t).as_expr()==t**3 and ((U*V)**2).trace()==2
 # Not an RK tableau: separates scalar pencil nilpotence from the mixed-word condition.
rational_small(); noncommuting_control()
# Exact two-coordinate rank/inertia formula in the strict case.
v,ga,cs,bj,bs=S.symbols('v ga cs bj bs',nonzero=True);ka=1+2*v/ga-(v/ga)**2
bb=S.Matrix([[bj,bs]]); cc=S.diag(cs-v,cs)
rr=S.Matrix([[-ga**2,0],[ga**2*(1-ka)*bj/bs,-ga**2]])
diff=(bb*cc*rr+bb*rr*cc-2*cs*bb*rr)
assert S.factor(diff[0]-ga**2*v*(1+ka)*bj)==0 and diff[1]==0
P=1009
def mod(r):
 u,v=S.sympify(r).as_numer_denom()
 return int(u)%P*pow(int(v)%P,-1,P)%P
def mat(M):
 return np.array(M.applyfunc(mod).tolist(),dtype=np.int64)
def mul(*ops):
 v=ops[0]
 for u in ops[1:]:v=v@u%P
 return v
def rank(M):
 a=np.array(M,dtype=np.int64)%P; n,m=a.shape;k=0
 for j in range(m):
  nz=np.flatnonzero(a[k:,j])
  if len(nz)==0:continue
  r=int(nz[0])+k;a[[r,k]]=a[[k,r]]
  a[k]=a[k]*pow(int(a[k,j]),-1,P)%P
  if k+1<n:a[k+1:]=(a[k+1:]-a[k+1:,j,None]*a[k][None,:])%P
  k+=1
  if k==n:break
 return k
def mk(m):
 pts=[(q,j) for q in range(1,m+1) for j in range(q)]
 nodes=[F(1,q*q) for q in range(1,m+1)]
 W=[prod(-v/(u-v) for v in nodes if v!=u) for u in nodes]
 n=len(pts); b=mat(S.Matrix([[F(W[q-1],q) for q,j in pts]]));B=np.diag(b[0])
 c=np.array([mod(F(2*j+1,2*q)) for q,j in pts],dtype=np.int64);C=np.diag(c)
 A=np.array([[mod(F(1,2*q)) if (q,j)==(u,k) else mod(F(1,q)) if q==u and k<j else 0 for u,k in pts] for q,j in pts],dtype=np.int64)
 R=(mul(C,A)-mul(A,C)-mul(A,A))%P;d=np.diag(R);Di=np.diag([pow(int(x),-1,P) for x in d])
 assert np.array_equal(R,np.diag(d))
 H,Tx,Tj=shadows(m); Tx,Tj=mat(Tx),mat(Tj)
 e=np.ones(n,dtype=np.int64); X=np.stack([np.array([pow(int(a),j,P) for a in c]) for j in range(m)],axis=1)
 Y=mul(mat(H.inv()),X.T,B)
 I=np.eye(n,dtype=np.int64);assert np.array_equal(mul(Y,X),np.eye(m,dtype=np.int64))
 U0=mul(Di,I-mul(X,Y));UA=mul(Di,A-mul(X,Tj,Y));UC=mul(Di,C-mul(X,Tx,Y))
 M=(mul(B,A)+mul(A.T,B)-mul(b.T,b))%P
 TM=mul(Di,np.diag([pow(int(x),-1,P) for x in b[0]]),M)
 assert not ( (mul(B,R,UA)+mul(B,R,UA).T-M)%P).any()
 # Actual degree-zero pure correction E=R^-1(A^2-X T_J^2 Y), checked here too.
 V=mul(Di,mul(A,A)-mul(X,Tj,Tj,Y))
 N,D=2*m-1,2*m-2
 cols={}
 for a in range(-2,D+1):
  cc=[]
  if a>=0:
   for h in range(a//2+1):
    j0=a-2*h
    for k in range(min(j0,N-j0)+1):
     cc.append([pow(int(z),h,P)*pow(int(x),k,P)%P for z,x in zip(d,c)])
  cols[a]=np.array(cc,dtype=np.int64).T if cc else np.zeros((n,0),dtype=np.int64)
  assert rank(cols[a])==cols[a].shape[1]
 for j in range(D+1):
  for u,cost in [(U0,2),(UA,1),(UC,1),(TM,1),(V,0)]:
   prev=cols[j-cost];assert rank(np.concatenate([prev,mul(u,cols[j])],axis=1))==prev.shape[1]

 if m>=4:
  F0=mul(Di,3*(mul(A,C)-mul(X,Tj,Tx,Y))-2*(mul(C,A)-mul(X,Tx,Tj,Y)))
  F1=mul(Di,3*(mul(I-C,A)-mul(X,np.eye(m,dtype=np.int64)-Tx,Tj,Y))-2*(mul(A,I-C)-mul(X,Tj,np.eye(m,dtype=np.int64)-Tx,Y)))
  z2=pow(2,-1,P);w=mul(b,R);r=mul(b,I-C,R)
  assert np.array_equal(mul(F0,e),(-3*z2*e)%P) and np.array_equal(mul(F0,c),(-c)%P)
  assert np.array_equal(mul(w,F1),(-3*z2*w)%P) and np.array_equal(mul(r,F1),(-r)%P)
  assert np.array_equal(mul(w,UA),np.zeros_like(w)) and np.array_equal(mul(r,UA),(-z2*w)%P)
  assert not mul(r,e).any() and not mul(w,c).any()
  tt=None
  for u in range(3):
   HH=(F0+u*F1)%P
   W1=(mul(HH,UA)-mul(UA,HH))%P
   if mul(b,W1,c).any() and mul(r,W1)[:,-1].any():tt=u;break
  assert tt is not None
  K=UA
  for a in range(7):
   obs=np.array([[mul(b,K,c)[0],mul(b,K)[0,-1]],[mul(r,K,c)[0],mul(r,K)[0,-1]]],dtype=np.int64)
   assert obs[1,0]==0 and rank(obs)==2
   K=(mul(HH,K)-mul(K,HH))%P

 r=rank(np.vstack([U0,UA,UC]));assert rank(U0)==n-m
 if m>=3:assert r>=n-m+(m-1)//2+int(any(tuple(mul(UC,X)[:,-1])))
 if m>=3:assert np.array_equal(mul(UA,c)[:,None],(-e*pow(2,-1,P)%P)[:,None])
 final=max(0,(2*m-1-m)//2)
 w=c.copy()
 for i in range(final):w=mul(R,w)
 for i in range(final):w=mul(U0,w)
 assert np.array_equal(w,c)
 print('midpoint true rational fixture (reduced modulo',P,') m,n,rankU0,rankstack:',m,n,rank(U0),r)
for m in [2,3,4,5,7,10]:mk(m)
print('all zero-/one-/two-drop tests passed')

```

Observed (m, stages, rank identity correction, rank stack): (2,3,1,2), (3,6,3,5), (4,10,6,9), (5,15,10,14), (7,28,21,27), (10,55,45,54). All zero-/one-/two-drop tests and seven bracket-depth minors in each indicated order ≥8 passed.

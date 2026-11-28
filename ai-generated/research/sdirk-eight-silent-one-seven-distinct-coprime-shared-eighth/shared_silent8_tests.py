"""Ordinary strict fifth plus masked rational cubic at the silent-eighth geometry."""
from shared_silent8_projection import *
from constant_front_tail import gammas
from front_tail_close import test_unit
from front_gauss_nonliteral import fterms

def split_fast(G,PH):
 J=ef(G)
 for n in range(len(PH)-1,-1,-1):
  if not PH[n]:continue
  U=ef(PH[n]);D=eguard(J,[U]);B=egcd(J,U)
  if D.degree()>0:yield unef(D),n
  J=B
  if J.degree()<=0:return
 assert J.degree()<=0

def pdiv_linear(a,b):
 assert len(b)==2 and b[-1]
 lc=b[-1];q=[E(0)]*(len(a)-1)
 while len(a)>=2:
  m=len(a)-2;z=a[-1]
  q=[v*lc+(z if i==m else E(0)) for i,v in enumerate(q)]
  a=[v*lc-(b[i-m]*z if m<=i<=m+1 else E(0)) for i,v in enumerate(a)]
  while a and not a[-1]:a.pop()
 assert len(a)<=1
 return q,a[0] if a else E(0)

def allowed_h4(G,PH,H4):
 r=[]
 H=[ef([x]) for x in H4]
 for N,j in split_fast(G,PH):
  U=ef(N)  # exact branch roots, possibly repeated
  dd=egcd(U,E(U.a.derivative(),U.b.derivative()))
  U=eexact(U,dd).monic()
  V=[ef(x) for x in PH[:j+1]]
  once=pseudo_e(V,H)
  line=pseudo_e(H,once) if len(once)==3 else once
  assert len(line)==2
  assert egcd(U,line[-1]).degree()==0
  _,rem4=pdiv_linear(H,line);assert etry(rem4,U) is not None
  V0,rem=pdiv_linear(V,line);assert etry(rem,U) is not None
  # The only common root with H4 on this exact component is the line root.
  # Remove any multiplicity, only when the remainder vanishes in the exact quotient.
  while len(V0)>1:
   V1,rem=pdiv_linear(V0,line)
   if etry(rem,U) is None:break
   V0=V1
  r.append((unef(U),list(map(unef,V0)),j))
 return r

@lru_cache(None)
def allowed(f,i):
 N,Phi,FT,FA=project(f,i)
 H4=frontdata(f,i)[8]
 Py=profile(f,i)[-1]
 B=bg(C(term0(H4,s).resultant(ats(Py),1)))
 G=unef(egcd(ef(N),ef(B)));D=unef(eguard(ef(N),[ef(B)]));PH=bsg(Phi)
 assert (len(G)-1,len(D)-1)==(36,649)
 print("shared silent8 H4 intersection",f,i,len(G)-1,len(D)-1,flush=True)
 exact=allowed_h4(G,PH,H4) if len(G)>1 else []
 general=[(P,PH[:j+1],j) for P,j in split_fast(D,PH)] if len(D)>1 else []
 assert [(len(P)-1,len(Q)-1,j) for P,Q,j in exact+general]==[(36,2,3),(311,3,3),(26,2,2)]
 print('exact shared silent8 fourth splits',f,i,len(N)-1,len(G)-1,len(D)-1,
       [(len(P)-1,len(Q)-1,j) for P,Q,j in exact+general],flush=True)
 return exact+general

def phase(f,i,p,t):
 fd=frontdata(f,i);assert len(gcdp(fd[8],exact_uc_y(fd[19])))==1
 _,_,_,D0,q0s,q1s,_=profile(f,i)
 checked=0
 for G,Phi,deg in allowed(f,i):
  assert len(Phi)>1
  for F,u in gammas(G,p,t):
   s0=trim([ev(list(map(F,a)),u) for a in Phi]);assert len(s0)==len(Phi)
   S=Tower(mon(s0));s=S.gen();v=S(u)
   checked+=1
   D,a0,a1=[ev(list(map(S,ps)),v) for ps in (D0,q0s,q1s)]
   g=1/D
   x=1-g;c=x-g*v
   a,b,ha=map(S,fd[5:8]);H4=list(map(S,fd[8]))
   pp=list(map(S,Lco));Q=[ev(pp,g*a)*a0,ev(pp,g*a)*a1]
   P=[ha*(a0+a1*a)*q*g**j for j,q in enumerate(pp)]
   h,T0,A0,T1,A1=fterms(S,fd,a,s,H4)
   A=add(sc(mul(T0,Q),h),mul(T1,P))
   B=add(sc(mul(A0,Q),h),mul(A1,P))
   D0s=list(map(S,nodal([a,s])))
   A,e=qr(A,D0s);assert not e
   B,e=qr(B,D0s);assert not e
   M,_=moments(S,g,-g*a0/a1,[g*a,x,c,g*s],3)
   R=polyres(S,A,B,3,3)
   assert test_unit(S,R,polyres(S,M,A,3,3),polyres(S,M,B,3,3))
 assert checked
 print('verified full shared silent eight:',f,i,p,checked,flush=True)
 return True

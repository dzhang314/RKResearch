"""Exact characteristic-zero filters followed by monic finite residual tests."""
from fast_support import *
from nofront_residue import residual
from verify_crt import check as crt_check
from itertools import product

def exact_U(H,R,conditions,cs=None):
 F=Remainder(H)
 try:
  U=F.trim(R);assert U and len(U)==6
  deg=[5]
  for B in conditions:
   B=F.trim(B)
   if not B:
    U=[E(1)];deg.append(0);break
   while len(U)>1:
    J=F.gcd(U,B)
    if len(J)<=1:break
    U,r=F.pseudo_div(U,J);assert not r and U
   deg.append(len(U)-1)
  if len(U)<=1:U=[E(1)]
  A=[]
  if cs is not None:
   A,B=map(F.trim,cs);assert A and B
   A=F.gcd(A,B)
   assert len(A)==2
  return [(H,U,A,deg)]
 except SplitE as e:
  A=e.Q;B=eexact(H,A).monic()
  return (exact_U(A,R,conditions,cs)+exact_U(B,R,conditions,cs))

@lru_cache(None)
def prepared(f,i):
 H=rec(f,i)
 assert crt_check(f,i,H)
 A,parts=split_g_fast(f,i,H)
 R,Ph,J,qa,qb,Gs,Cs,T4,H4=reg_data(f,i)
 # Keep only roots satisfying actual nonzero guards at each small diagonal.
 Ls=list(map(lambda L:list(map(ef,L)),guard_coeffs()))
 Lz=contact_support(f,i)[1]
 gs={'c':Ls[0],'d':Ls[1],'phi3':Ph[-1],'qz':Lz}
 X=E(P([0,1]));H4=[ef([a]) for a in frontdata(f,i)[8]]
 L4s=[v*epow(X,j) for j,v in enumerate(Lco)]
 hx=(H4,L4s)
 S=[(A,R,[],[5],['regular'])]
 for H,flags in parts:
  pre=[gs[k] for k in flags if k!='h4']
  S.extend((B,W,C,ds,flags) for B,W,C,ds in exact_U(H,R,pre,hx if 'h4' in flags else None))
 print('exact retained U / fourth zero-factor degrees:',
       f,i,[(G.degree(),len(U)-1,len(J)-1,ds,flags) for G,U,J,ds,flags in S],flush=True)
 return S,Ph,J,tuple(map(Vcoeff,(qa,qb)))

def mod_part(f,i,p,t,G,R,C,Ph,J,q0,q1,flags):
 dG=red_e(G,p,t)
 assert dG.degree()==G.degree() and int(dG.leading_coefficient())==1
 warnings=[];nU=0;nS=0;nG=0
 for M,F,g in U_gammas(dG,p,t):
  nG+=1
  evg=lambda a:F(red_e(a,p,t))
  U0=trim(list(map(evg,R)))
  if len(U0)!=len(R):
   warnings.append(('tail leading',M.degree(),str(M)));continue
  if not C:C0=[]
  else:
   C0=trim(list(map(evg,C)))
   if len(C0)!=len(C):
    warnings.append(('H4 lowering leading',M.degree(),str(M)));continue
   C0=mon(C0)
  if len(U0)==1:continue
  for Upoly in ff_factors(F,U0,p):
   nU+=1;U=Tower(Upoly);u=U.gen();g0=U(g)
   at=lambda A:ev([U(evg(z)) for z in A],u)
   Phi=trim([at(a) for a in Ph])
   if len(Phi)!=4:
    warnings.append(('fourth leading',M.degree(),len(Upoly)-1,str(M)));continue
   if C0:
    Phi,r=qr(Phi,list(map(U,C0)));assert not r and len(Phi)==3
   J0=trim([at(a) for a in J]);S=gcdp(Phi,J0)
   if len(S)<=1:continue
   nS+=1
   W=Nested(mon(S));s=W.gen();gg=W(g0);uu=W(u)
   Y0=lambda X:W(at(X))
   qa,qb=Y0(q0),Y0(q1)
   B,A,D=residual(W,gg,uu,s,f,i,qa,qb)
   R0=[polyres(W,B,D,3,3),polyres(W,A,D,3,3),polyres(W,B,A,3,3)]
   if not test_unit(W,*R0):
    warnings.append(('fifth',M.degree(),len(Upoly)-1,len(S)-1,str(M)))
 print('monic finite residual part',f,i,p,G.degree(),flags,(nG,nU,nS),warnings,flush=True)
 return warnings

def primes(f,i,G,R,Ph):
 from sympy import isprime
 H=syl(R,Ph[-1]);assert H
 candidates=[(1103,161),(1129,203),(1559,529)]
 candidates.extend((p,pow(2,(p+1)//4,p)*((p+1)//2)%p)
                  for p in range(8191,9000,8) if isprime(p))
 for p,t in candidates:
  assert isprime(p) and 2*t*t%p==1
  try:
   A,B,L=map(lambda Z:red_e(Z,p,t),(G,H,R[-1]))
   if A.degree()!=G.degree() or B.degree()!=H.degree() or L.degree()!=R[-1].degree():continue
   n=A.gcd(B*L).degree()
   if n:
    print('regular leading prime rejected (accidental reduction)',f,i,p,n,flush=True)
    continue
   yield p,t
  except (ValueError,ZeroDivisionError):
   continue

def comprehensive(f,i):
 T,Ph,J,Q=prepared(f,i)
 q0,q1=(list(map(ef,X)) for X in Q)
 details=[]
 for G,R,H,_,flags in T:
  assert G.degree()>0
  pool=primes(f,i,G,R,Ph) if 'regular' in flags else [(1103,161)]
  w=None
  for p,t in pool:
   w=mod_part(f,i,p,t,G,R,H,Ph,J,q0,q1,flags)
   if not w:
    details.append((G.degree(),flags,p));break
  else:raise ArithmeticError((f,i,'unsettled exact branch',G.degree(),flags,w))
 print('complete no-active-literal arithmetic exclusion',f,i,details,flush=True)
 return details

"""Exact diagonal support splitting for the no-front arithmetic projection."""
from nofront_residue import *
from exact_crt import rec
from shared_silent8_projection import etry,epow,norm_irreducible
from time import perf_counter

@lru_cache(None)
def contact_support(f,i):
 r,q0,q1,sa=tail(f,i)
 a=C(frontdata(f,i)[5]);z=g*a
 qp=coefficients_e(can(q0+q1*z));R=coefficients_e(r)
 zraw=syl(R,qp);assert zraw
 G0=[ef(Gcoeff(v)) for v in sa]+[R[-1]]
 Z=e_sf(eguard(zraw,G0))
 print('exact q(z) forbidden U carrier',f,i,Z.degree(),[(h.degree(),m) for h,m in enorm(Z).factor()[1]],flush=True)
 return Z,qp

def separate_components(C):
 out=[]
 for N,_ in enorm(C).factor()[1]:
  A=egcd(C,E(N))
  if A.degree()>0:out.append(A)
 assert sum(a.degree() for a in out)==C.degree()
 return out

@lru_cache(None)
def support(f,i):
 R,Ph,J,qa,qb,G0,Sp,T4,H4=reg_data(f,i)
 Zr,Zp=contact_support(f,i)
 H4=e_sf(eguard(H4,G0))
 print('H4 and guard intersections',f,i,H4.degree(),
       [(n,egcd(H4,C).degree()) for n,C in zip(('c','d','phi3','qz'),[*Sp,T4,Zr])],flush=True)
 grouping=[]
 for n,C in zip(('c','d','phi3','h4','qz'),[*Sp,T4,H4,Zr]):
  L=[]
  for A,ns in grouping:
   W=egcd(A,C)
   if W.degree()>0:
    A=eexact(A,W).monic();C=eexact(C,W).monic()
    L.append((W,ns+[n]))
   if A.degree()>0:L.append((A,ns))
  if C.degree()>0:
   L.extend((F,[n]) for F in separate_components(C))
  grouping=L
 print('exact special Γ partition',f,i,[(M.degree(),s) for M,s in grouping],flush=True)
 return grouping,G0,R,Ph,Zp

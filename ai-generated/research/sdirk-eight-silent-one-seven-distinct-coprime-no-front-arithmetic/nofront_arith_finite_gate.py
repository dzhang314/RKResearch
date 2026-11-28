"""Certificate the exact arithmetic-tail norm is not the zero rational function."""
from nofront_arith_cross import *
from shared_arith_projection import prim

def cv_eval(e,γ):return E(e.a(γ),e.b(γ))

def lifted_coeffs(Z,γ):
 return [[cv_eval(v,γ) for v in ps] for ps in E_su(Z)]

def determinant_content(D):
 B={}
 for (j,k,l,m,n),v in D.to_dict().items():
  assert not l and not m
  A=B.setdefault(j,[{},{}])[n];A[k]=v
 def p(u):return P([u.get(i,Q(0)) for i in range(max(u,default=-1)+1)])
 G=E(0)
 for A in B.values():G=egcd(G,E(*map(p,A)))
 return G


def verify(f,i):
 Ph,T,A,D=fronts(f,i)
 R,q0,q1,safe=tail(f,i)
 r=coefficients_e(R)
 assert prim(R)[0].degree()==0 and determinant_content(D).degree()==0
 J=fold(T.resultant(D,0))
 assert J.degrees()==(0,21 if f else 23,9,30,1)
 for gg in (Q(1),):
  rv=list(map(lambda a:cv_eval(a,gg),r))
  if not rv[-1]:continue
  X=UContext(rv)
  P0=[X.e(a) for a in lifted_coeffs(Ph,gg)]
  Y0=[X.e(a) for a in lifted_coeffs(J,gg)]
  # Preserve the nominal generic coefficient ranges, or try another specialization.
  if len(P0)!=4 or not P0[-1] or not Y0[-1]:continue
  Z=prem_s(Y0,P0)
  if not Z or len(Z)!=3:continue
  F=resultant(P0,Z,X)
  if not F:continue
  N,sz=X.norm_numerator(F)
  if not N:continue
  LC,lc=X.norm_numerator(P0[-1])
  assert LC
  print('exact nonzero no-front arithmetic norm:',f,i,str(gg),J.degrees(),
        sz,list(map(bool,(N.a,N.b))),flush=True)
  return True
 raise ArithmeticError('no successful specialized nonzero norm')

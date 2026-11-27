#!/usr/bin/env python3
"""Exact reflection fiber computation with a symmetric early hull and an endpoint last."""
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
import sympy as S
from math import prod
from flint import fmpq_mpoly_ctx,fmpq
p=Path(__file__).with_name("check-symmetric-midpoint.py")
s=spec_from_file_location('mid',p)
A=module_from_spec(s);s.loader.exec_module(A)
P4=A.P4
C=A.C
z,r,t,x=S.symbols("z r t x")
m=z/2
pN=13*z**4/S.Integer(1120)+(r+4-5*z)*z*z/80
pD=3*z*z/S.Integer(40)+(r+4-5*z)/12
hN=r+2-z;hD=4-z
J1=z**4*pD/80-pN*z*z/12
R=(x-1)*(x*x-4*x+r)
Kmom=[sum(v*z**(i[0]+j)/(i[0]+j+1) for i,v in S.Poly(R,x).terms()) for j in (0,1,2)]
c=m+t
K=pD*(Kmom[2]+(c-3*m)*Kmom[1]+(c*c-3*m*c+3*m*m)*Kmom[0])-pN*Kmom[0]
W0=(5-z)*hN-r*hD
W1=(z-1)*hD-hN
M=2-r
L=c**3-9*c*c+18*c-6
F=L*(c*hD-hN)*K+(4*M+(4-M)*(c-1))*J1*(W0+W1*c)
H=pD*t*t-pN
res=S.factor(S.resultant(H,F,t))
sc,cols=S.factor_list(res)
assert S.expand(sc*prod(f**n for f,n in cols)-res)==0
print('endpoint projection factors',[(S.Poly(f,z,r).total_degree(),S.degree(f,z),S.degree(f,r),k,f if S.degree(f,z)<10 else '') for f,k in cols],flush=True)
ss=lambda f:C.from_dict({tuple(int(a) for a in m):fmpq(str(q)) for m,q in S.Poly(f,z,r).terms()})
excluded=[
 z,z-4,pD,r-2,r-3,r-4,J1,
 S.resultant(H,S.expand(R.subs(x,c)),t), # either early endpoint aliased to a terminal
 S.resultant(H,c*hD-hN,t), # either early endpoint aliased to the ghost
]
FF=A.strip_factors(ss(res),tuple(ss(q) for q in excluded))
print('active endpoint factors',[(A.info(f),k) for f,k in FF.factor()[1]],flush=True)
records=[]
for f,j in FF.factor()[1]:
 for q,k in P4.factor()[1]:
  records.append(A.verify_projected_roots(f.resultant(q,"r")))
assert sorted(records)==[([2,39],["4"]),([12],[])]

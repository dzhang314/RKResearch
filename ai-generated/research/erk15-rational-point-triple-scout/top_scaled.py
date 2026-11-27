#!/usr/bin/env python3
"""Scaled exact first-four pressure elimination; avoid rational function swell."""
from symbolic_pressure import *
from sympy import resultant,gcd
def coeff(y,u,v):
    return [y*y*(3*v-2*y)/(6*u*(v-u)),
            y*y*(2*y-3*u)/(6*v*(v-u))]
M=coeff(a,a,t);m=t*t/(2*a)
KA,KC,KD0=[fixed(y)for y in [a,t,d]]
WA,WC=-a**3*M[0]/6,-a**3*m/6
WDs,WEs=[cancel(WA*Z[0]+(y-A)*(WC*Z[1]-WA*Z[0])/(C-A))for y in (D,E)]
# v-components of the two opposed profiles, independent of the physical split.
SK=6*(KA-a**4/4)/a**3
SW=6*(WA+a**4/12)/a**3
ca,cc=coeff(d,a,t)
KD=[(a**4*M[0]/4+KC*M[1])*Z[0],(a**4*m/4)*Z[1],
    Z[2]*(KA*ca+KC*cc)+SK*WDs]
KW=[(-a**4*M[0]/12+WC*M[1])*Z[0],(-a**4*m/12)*Z[1],
    Z[2]*(WA*ca+WC*cc)+SW*WDs]
# Only the old scalar total at D sees WD=WDs/ZD; its E-row tap
# is a known cubic-cardinal tap divided by a fixed scalar denominator.
J0=[a,t,d]
ee=1-E
q=[cancel((Z[3]*(ee**4/4-(v+w)*ee**3/3+v*w*ee**2/2)+pE)/(u*(u-v)*(u-w)))
       for j,u in enumerate(J0) for v,w in [[x for i,x in enumerate(J0)if i!=j]]]
KD.append(cancel(sum(k*u for k,u in zip([KA,KC,KD0],q))+SK*WEs))
KW.append(cancel(WA*q[0]+WC*q[1]+WDs*q[2]/Z[2]+SW*WEs))
pres=lambda t:cancel(sum(n/prod(y-h for h in Y if y!=h) for n,y in zip(t,Y)))
p0,p1,p2=[Poly(p.as_numer_denom()[0],D,E).primitive()[1].as_expr() for p in (top,pres(KD),pres(KW))]
degs=[(Poly(q,D,E).degree(D),Poly(q,D,E).degree(E))for q in (p0,p1,p2)]
print("Necessary pressure bidegrees:",degs)
poly0=lambda fun: Poly(fun,D).monic()
A0=2*D-1
A1=102*D**2-102*D+11
A2=5271*D**2-4864*D+193
rs1=resultant(p0,p1,E)
rs2=resultant(p0,p2,E)
assert poly0(gcd(rs1,rs2))==poly0(A0**8*A1**8*A2**3)
print("Top projected gcd: (2D−1)^8 (102D²−102D+11)^8 (5271D²−4864D+193)^3, up to units.")
num=lambda x:cancel(x).as_numer_denom()[0]
quad0=Poly(num(det),D,E).primitive()[1].as_expr()
z1=resultant(quad0,num(S),E); z2=resultant(quad0,num(P),E)
assert poly0(gcd(z1,z2))==poly0(A0**2*A1**2)
z3=[Poly(s.subs(D,Q(1,2)),E).monic()for s in (det,S,P)]
assert z3[0].gcd(z3[1]).gcd(z3[2])==Poly(E**2-E+Q(11,102),E)
rp=resultant(num(Rnum),num(Rden),E)
assert poly0(rp)==poly0(A0**2*A1**2*A2**3)
assert cancel(H[3]-37*A0*A1/(83349000000000*(E-1)))==0
from math import isqrt
for da,db,dc in [(102,-102,11),(5271,-4864,193)]:
    discr=db*db-4*da*dc
    assert isqrt(discr)**2!=discr
print("Singular moment pivot tests and nonsquare quadratics verified.")

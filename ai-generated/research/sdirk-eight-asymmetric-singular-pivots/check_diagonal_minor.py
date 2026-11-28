#!/usr/bin/env python3
import sympy as S
from math import isqrt,prod
x,q=S.symbols('x q')
A=-63*x*x*q+21*x*x-70*x*q**3-210*x*q*q-138*x*q-30*x+245*q**5+805*q**4+986*q**3+546*q*q+129*q+9
B=-525*x*x*q+525*x*x-1750*x*q**3-5670*x*q*q-3150*x*q-630*x+3675*q**5+13825*q**4+17970*q**3+9990*q*q+2259*q+153
T=-105*x*q-15*x+175*q**3+255*q*q+105*q+9
J1=35*q*q-3;J2=35*q*q+30*q+3
J3=1225*q**8+9450*q**7+24640*q**6+25230*q**5+9639*q**4-480*q**3-1212*q*q-360*q-36
D=175*q**4+588*q**3+279*q*q+72*q+6
N=J2*(35*q**4+140*q**3+131*q*q+40*q+6)
assert S.expand(S.resultant(A,B,x)+1344*J1*J2*J3)==0
a=S.Poly(A,x).nth(2);b=S.Poly(B,x).nth(2)
assert S.expand(a*B-b*A-84*(5*D*x-N))==0
assert S.expand(5*D*(175*q**3+255*q*q+105*q+9)+(-105*q-15)*N -
                20*q*q*(q+3)*J1*J2)==0
n=abs(int(S.resultant(D,N,q)))
assert n==2**23*3**3*5**3*7**3*59*6359
for p,qq,xx,bad in [(59,9,50,2),(6359,2219,3726,0)]:
 assert all(p%d for d in range(2,isqrt(p)+1))
 G=S.gcd(S.Poly(D,q,modulus=p),S.Poly(N,q,modulus=p)).monic()
 assert G==S.Poly(q-qq,q,modulus=p)
 H=S.gcd(S.Poly(A.subs(q,qq),x,modulus=p),S.Poly(B.subs(q,qq),x,modulus=p)).monic()
 assert H==S.Poly((x-xx)*(x-bad),x,modulus=p)
 assert int(T.subs({q:qq,x:bad}))%p==0 and int(T.subs({q:qq,x:xx}))%p!=0
 print('exception exact minor',p,qq,xx)

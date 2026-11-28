import sympy as S
B,Y=S.symbols('B Y')
j4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
j5=lambda x:(2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)
J4,J5=(S.Poly(q(Y),Y,domain=S.QQ)for q in (j4,j5))
u,v,g=S.gcdex(J4,J5)
assert g.as_expr()==1
print('Bezout degrees',u.degree(),v.degree(),flush=True)
K=S.QQ.frac_field(B)
T=S.Poly(j5(Y)*j4(B)-j5(B)*j4(Y),Y,domain=K)
Q=T.exquo(S.Poly(Y-B,Y,domain=K)).monic()
I=S.Poly(sum(Q.nth(i)*Y**(i+1)/S.Integer(i+2)for i in range(5)),Y,domain=K)
inv=S.Poly(u.as_expr()+j5(B)/j4(B)*v.as_expr(),Y,domain=K)
assert (inv*S.Poly(j4(Y),Y,domain=K)).rem(Q).as_expr()==1
E=(I*inv).rem(Q)
assert S.cancel(E.nth(3)-(B-1)**2/(6*j4(B)))==0
for i in range(4):
    d=S.Poly(S.cancel(E.nth(i)).as_numer_denom()[1],B,domain=S.QQ)
    assert S.Poly(j4(B)**2,B,domain=S.QQ).rem(d).is_zero
print('Exact Jacobi cubic coefficient (B−1)^2/(6 J4(B)); all symbolic denominators guarded',flush=True)

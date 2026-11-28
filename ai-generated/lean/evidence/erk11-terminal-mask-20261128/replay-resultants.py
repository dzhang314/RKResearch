import sympy as s
u,v,x=s.symbols('u v x')
M=s.Matrix([[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]])
vec=lambda x: s.Matrix([x**i for i in range(5)])
K=(vec(x).T*M*vec(v))[0].expand()
Q=s.div(K-K.subs(x,u),x-u,x)[0]
F0=K.subs(x,u).expand()
F1=(u*(6*Q.coeff(x,1)+10*u*Q.coeff(x,2)+13*u**2*Q.coeff(x,3))+24*Q.subs(x,u/2)).expand()
F2=((1-u)*(-6*s.diff(Q,x).subs(x,1)+5*(1-u)*s.diff(Q,x,2).subs(x,1)-13*(1-u)**2*Q.coeff(x,3))+24*Q.subs(x,(1+u)/2)).expand()
for i,F in enumerate([F0,F1,F2]):
 print(i,'coeffs=',[s.factor(F.coeff(v,j)) for j in range(5)], 'degree',s.Poly(F,v).degree())
G=s.factor(s.resultant(F0,F1,v))
H=s.factor(s.resultant(F0,F2,v))
print('G=',G)
print('H=',H)
print('gcd=',s.factor(s.gcd(G,H)))
print('modular')
for p in [11,13,17,19,23,29,31,37,41,43,47]:
 g=s.Poly(G,u,modulus=p);h=s.Poly(H,u,modulus=p)
 print(p,g.degree(),h.degree(),g.gcd(h).as_expr(), (g.is_zero,h.is_zero))
print('ref ct',s.expand(F2+F1.subs({u:1-u,v:1-v},simultaneous=True)))

gram=s.Matrix(5,5,lambda i,j:s.Rational(1,(i+j+2)*(i+j+3)))
assert gram*(210*M)==s.eye(5)
assert s.expand(K-K.subs({x:1-x,v:1-v},simultaneous=True))==0
assert s.expand(F2+F1.subs({u:1-u,v:1-v},simultaneous=True))==0
for poly in (G,H):
    assert s.Poly(poly,u).degree()==s.Poly(poly,u,modulus=13).degree()==24
assert s.Poly(G,u,modulus=13).gcd(s.Poly(H,u,modulus=13)).as_expr()==1
print('independent Gram, reflection, both degree-24 resultants and mod-13 gcd verified')

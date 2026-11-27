import sympy as S
p,q,r,X=S.symbols('p q r X')
a=2*p/3
l=lambda x:3*x*x*(3*p-2*x)/(4*p*p)
g=lambda x:-x**4/4+(p+a)*x**3/3-p*a*x*x/2
c=q*(q-p)/(a*(p-a))
d=q*(q-a)*(q-p)
mom=lambda R:S.integrate(R,(X,0,1))
I= (mom(X**2*(X-p)*(X-q))/mom(X*(X-p)*(X-q))).cancel()
print('r',S.factor(I))
weights={}
for w in (p,q,r):
    K=S.prod(X-y for y in (0,p,q,r) if w!=y)
    weights[w]=mom(K).factor()/K.subs(X,w)
V=sum(weights[x]*l(x)for x in (p,q,r))
W=sum(weights[x]*g(x)for x in (p,q,r))
P=S.factor((d*V-c*W).cancel().subs(r,I).cancel())
print('compatibility determinant',P)
for v in range(1,10):
    pp=S.Rational(v,10)
    z=S.factor(S.fraction(P.subs(p,pp).cancel())[0])
    if z==0:continue
    print(pp,z,S.nroots(z) if z.has(q) else '-')

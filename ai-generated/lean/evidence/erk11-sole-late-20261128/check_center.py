#!/usr/bin/env python3
"""Independent rational moment and Sturm–Tarski replay of the central case."""
import sympy as s
x,a,b,S,T=s.symbols('x a b S T')
p=x**2*(x-a)**2
q=(1-x)**2*(1-x-b)**2
def integrate(f, upper):
    return s.Poly(f,x).integrate().as_expr().subs(x,upper)
def moment(f):return integrate(f,1)
P=integrate(p,x)
Q=integrate(q,1)-integrate(q,x)
H=moment(P*q)
assert s.expand(H-moment(p*Q))==0
C,B=moment(x*p*Q),moment(x*P*q)
D0,D1,D2=[moment(x**j*p*q) for j in range(3)]
gram=s.Matrix(5,5,lambda i,j:s.Rational(1,(i+j+2)*(i+j+3)))
v=lambda z:s.Matrix([z**k for k in range(5)])
kernel=(v(a).T*gram.inv()*v(1-b))[0]
def sym(f):
    pol,rem,gens=s.symmetrize(s.expand(f),[a,b],formal=True)
    assert rem==0
    return s.expand(pol.xreplace({gens[0][0]:S,gens[1][0]:T}))
F=s.Poly(sym(871363785600000*(D2*H**2-D1*H*(B+C)+D0*B*C)),T)
E=s.Poly(sym(19800*(kernel*moment(P*Q)-a**4*b**4/900)),T)
assert F.degree()==E.degree()==6
def bez(i,j):
    return s.expand(sum(F.nth(i+j+1-k)*E.nth(k)-F.nth(k)*E.nth(i+j+1-k)
                        for k in range(min(i,j)+1) if i+j+1-k<=6))
M=s.Matrix(6,6,bez)
D=s.Poly(M.det(method="domain-ge"),S)
A=s.Poly(M.minor(0,0,method="domain-ge"),S)
B=s.Poly(-M.minor(0,1,method="domain-ge"),S)
assert D.degree()==34
R=D.sqf_part()
assert R.degree()==32
Z=(A*(s.Poly(S**2,S)*A-4*B)).rem(R)
def changes(P,Q,direction):
    degsigns=[]
    while not P.is_zero:
        degsigns.append(int(s.sign(P.LC()))*direction**P.degree())
        if Q.is_zero:break
        P,Q=Q,(-P.rem(Q)).primitive()[1]
    return sum(a!=b for a,b in zip(degsigns,degsigns[1:]))
def count(P,Q):return [changes(P,Q,d) for d in (-1,1)]
ordinary=count(R,R.diff())
signed=count(R,(R.diff()*Z).rem(R))
assert ordinary==[19,13] and signed==[13,19]
print("exact moment/bilinear replay: determinant degree",D.degree(),"squarefree",R.degree())
print("Sturm variations",ordinary,"and discriminant sign-query variations",signed)
print("Every possible real determinant root has a strictly negative discriminant.")

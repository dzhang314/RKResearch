from sympy import Rational as Q, Symbol, diff, integrate, div, expand, solve
X, a,b,c=map(Symbol,['X','a','b','c'])
R=a*X**2+b*X+c
assert solve([integrate(X*R,(X,0,1)),integrate(X**2*R,(X,0,1))],(b,c))=={b:-6*a/5,c:3*a/10}
P=X**2-Q(6,5)*X+Q(3,10)
J=integrate(X*P,X)
assert diff(J,X)==X*P or expand(diff(J,X)-X*P)==0
q,r=div(J,P,X)
assert q==X**2/4-X/10-Q(9,200)
assert r==Q(27,2000)-3*X/125
print("P =",P)
print("J(XP) =",J)
print("quotient =",q,"remainder =",r)

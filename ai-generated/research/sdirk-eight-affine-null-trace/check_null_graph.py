from sympy import symbols,Rational,resultant
from math import gcd
X=symbols('X')
H=lambda x:70*x**4-140*x**3+90*x*x-20*x+1
Q=lambda n,d:4*n**3-12*n*n*d+3*n*d*d+2*d**3
d=X
out=[]
for gam,e,a,c in ((d,1-d,2-3*d,1-d),(1-d,1-d,3*d-1,d),(Rational(1,2),Rational(1,2),2*d-Rational(1,2),d)):
    fs=[H(a),Q(c-gam,gam)]
    norms=[abs(int(resultant(H(d),f,d).as_numer_denom()[0])) for f in fs]
    out.append((tuple(norms),gcd(*norms)))
    print(gam,e,a,c,'norms',norms,'gcd',gcd(*norms))
assert out==[((1016064000000,849674),14)]*2+[((848931890625,917773),1)]

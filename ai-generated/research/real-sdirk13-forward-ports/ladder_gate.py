"""Exact scalar obstruction to a seven-site degree-12 rule with five odd ladder pins."""
from itertools import combinations
import sympy as s
g,x=s.symbols('g x')
F=s.Poly(s.prod(x-(2*i-1)*g for i in range(1,6)),x)
M=[s.Poly(sum(F.nth(k)/s.Integer(k+j+1) for k in range(6)),g,domain=s.QQ) for j in range(8)]
def det(Q):
    a,b,c=Q
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
rows=[[M[j+i]for i in range(3)]for j in range(6)]
G=None
for I in combinations(range(6),3):
    D=det([rows[i]for i in I]);G=D if G is None else G.gcd(D)
    print('minor rows',I,'degree',D.degree(),'normalized gcd',G.monic().expr)
    if G.degree()==0:break

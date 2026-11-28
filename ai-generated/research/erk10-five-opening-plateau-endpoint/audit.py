"""Exact replay of the plateau ingress constants and triangular exit."""
from argparse import ArgumentParser
from pathlib import Path
import json
import sympy as S

a,b,z,r = S.symbols("a b z r")
assert S.expand(r**2-2*r**3+r**4-r**2*(r-1)**2)==0
H5=S.Matrix([[S.Rational(1,i+j+1) for j in range(5)] for i in range(1,6)])
assert H5.det()==1/(S.Integer(2)**12*3**7*5**5*7**4)
assert S.integrate(z*(1-z),(z,0,1))==S.Rational(1,6)
print("paid shifted Hilbert 5, actual residual second difference, and weighted nominal 1/6 verified")

Q=1-(1-z/a)*(1-z/b)
assert all(S.cancel(Q.subs(z,i)-bit)==0 for i,bit in [(0,0),(a,1),(b,1)])
# Nonzero y positions separated by physical y=0 slots, at arbitrary scores.
r1,r2,r3,r4,r5,r6,w0,w1,w2,w3=S.symbols("r1 r2 r3 r4 r5 r6 w0 w1 w2 w3")
Y=S.diag(a,0,0,b)
K=S.Matrix([[0,0,0,0],[r1,0,0,0],[r2,r3,0,0],[r4,r5,r6,0]])
w=S.Matrix([w0,w1,w2,w3])
u=K*Y*w-Y**2*w/2
idx=[0,3]
L=K.extract(idx,idx)-Y.extract(idx,idx)/2
assert S.cancel(L.det()-a*b/4)==0
assert all(S.cancel(c)==0 for c in L.inv()*u.extract(idx,[0])-(Y*w).extract(idx,[0]))
print("global label mask and strict principal triangular inverse checked symbolically")

parser=ArgumentParser()
parser.add_argument("--f17",type=Path)
args=parser.parse_args()
if args.f17:
    d=json.loads(args.f17.read_text())
    A,w=d["A"],d["b"]
    assert len(A)==len(w)==15
    x=[sum(row)%17 for row in A]
    assert x[max(i for i in range(5,15) if w[i]%17)]==1
    V=[(sum((A[i][j] if j<len(A[i]) else 0)*w[i] for i in range(5,15))
        -(1-x[j])*w[j])%17 for j in range(5,15)]
    assert V==[0]*10
    print("published F17 literal: all ten raw first adjoint discrepancies zero; last live clock is 1")

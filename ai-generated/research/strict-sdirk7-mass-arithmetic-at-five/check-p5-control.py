#!/usr/bin/env python3
"""A regular arithmetic split clock core over Q_5, not a rational tableau."""
from pathlib import Path
from runpy import run_path
p=run_path(str(Path(__file__).with_name('check-arithmetic-at-five.py')))
F,Fp=p['F'],p['F'].derivative(0)
R,D,N,Q1,Q0=p['R'],p['D'],p['N'],p['Q1'],p['Q0']
C,u=p['C'],p['u']
B=p['B']
m,norm_e=1,2
e=3
def val(q):
    q=int(q)
    assert q
    v=0
    while q%5==0:q//=5;v+=1
    return v,q%5
def at(q,x):
    return int(q(x,m,norm_e,0))
assert at(F,3)%5==0 and at(Fp,3)%5
U,Q=3,5
for _ in range(16):
    (U,)=tuple(U+i*Q for i in range(5) if at(F,U+i*Q)%(Q*5)==0)
    Q*=5
assert (U,Q)==(564230841913,762939453125)
assert val(at(R,U))==(4,1) and val(at(D,U))[0]==1
assert val(at(B[3],U))[0]<17
for y in [C.constant(1),u,2*u-1,C.constant(e)]:
    assert val(at(N-D*y,U))[0]<17
    assert val(at(B[3]*D*D*y*y+Q1*D*y+Q0,U))[0]<17
assert val(at(B[3]*N*N+Q1*N+Q0,U))[0]<17
h=[e,1,U,2*U-1]
assert all(val(a-b)[0]<17 for i,a in enumerate(h) for b in h[i+1:])
print("Q5 clock control: eta=2, m=1, u≡564230841913 (mod 5^17)")
print("nonzero R has v5=4 and unit square residue; all seven clocks distinct")

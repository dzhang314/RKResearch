#!/usr/bin/env python3
"""Check three entire exact B factors that never have five distinct nonendpoints."""
from flint import fmpq,fmpq_poly,fmpz_poly
from pathlib import Path
from sys import argv
assert len(argv)==4, 'usage: check-jacobi-guards.py gamma5-guards pair-guards guard-directory'
def rz(f):return fmpz_poly([int(x)for x in Path(f).read_text().split()])
def rp(f):return fmpq_poly([fmpq(x)for x in Path(f).read_text().split()]).numer()
B=fmpz_poly([0,1])
J4=42*B**4-84*B**3+56*B*B-14*B+1
J5=(2*B-1)*(66*B**4-132*B**3+84*B*B-18*B+1)
Q=rp(Path(argv[3])/'Gclock derivative.txt')
fs=[list(rz(f).factor()[1])for f in argv[1:3]]
for f in fs:
    assert [h.degree()for h,k in f]==[4,4,16,24,24,28,60,60]
    assert f[0][0]==J4
    assert f[1][0].gcd((J4+J5)*(J4-J5))==f[1][0]
    assert f[3][0].gcd(Q)==f[3][0]
assert all(fs[0][j][0]==fs[1][j][0] for j in range(7))
print('J4, endpoint-contact and multiple-ordinary-clock factors excluded in both charts')

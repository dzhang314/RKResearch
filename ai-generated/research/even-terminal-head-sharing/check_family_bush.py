"""Check the literal diagonal and exact first unpaid bush without printing huge fractions."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json, sys
if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
for filename in sys.argv[1:]:
    t=json.loads(Path(filename).read_text())
    s,p=t['stages'],t['order']
    A,w,d,e=t['a_integer'],t['b_integer'],t['a_denominator'],t['b_denominator']
    assert s==len(A)==len(w) and all(len(row)==s for row in A) and d>0 and e>0
    assert all(type(x) is int for x in w) and all(type(x) is int for row in A for x in row)
    assert all(4*A[i][i]==d and all(x==0 for x in A[i][i+1:]) for i in range(s))
    r=Fraction((p+1)*sum(v*sum(row)**p for row,v in zip(A,w)),e*d**p)-1
    assert r and r==Fraction(t['next_bush_defect'])
    print(f'order {p}, {s} stages: nonzero next-bush defect, sign {1 if r>0 else -1}, SHA-256 {sha256(str(r).encode()).hexdigest()}')

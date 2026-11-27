"""Independent exact triangularity, common diagonal, and next-bush checks."""
from fractions import Fraction as Q
import json, sys
from pathlib import Path
if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
for path in sys.argv[1:]:
    t=json.loads(Path(path).read_text())
    m,p=t['stages'],t['order']
    A,w,d,e=t['a_integer'],t['b_integer'],t['a_denominator'],t['b_denominator']
    assert m==len(A)==len(w) and all(len(row)==m for row in A) and d>0 and e>0
    assert all(type(v) is int for v in w) and all(type(v) is int for row in A for v in row)
    assert all(4*A[i][i]==d and all(x==0 for x in A[i][i+1:]) for i in range(m))
    bdef=Q((p+1)*sum(b*sum(row)**p for row,b in zip(A,w)),e*d**p)-1
    assert bdef and bdef==Q(t['next_bush_defect'])
    print(f'{m} stages, order {p}, diagonal 1/4, cleared next-bush defect {bdef}',flush=True)

"""Rule out a second whole size-eight pure row of the fixed fifteen-row stem."""
from pathlib import Path
import sys

if len(sys.argv) != 3:
    raise SystemExit("usage: check_only_port.py REFINE_PORTS_WORKDIR MOVABLE_PORT_SOURCE_DIR")
sys.path.insert(0, str(Path(sys.argv[2]).resolve()))
from check_stem15 import I, B, Z, O, construct, dot

A, _, _, _ = construct()
c = [sum(row,Z) for row in A]
first = [None]*15
cats = []
for n in range(1,9):
    past=cats[:]
    expected=[x**(n-1) for x in c]
    def rec(remaining,j,prod):
        if not remaining:
            actual=[prod[i]-expected[i] for i in range(15)]
            for i,err in enumerate(actual):
                if i==13:
                    assert not err.sign(),'known certified port contradicts profile'
                elif first[i] is None and err.sign():
                    first[i]=(n,err.inf().bit_length()-1-B)
            cats.append((n,[n*dot(row,prod) for row in A]))
            return
        for k in range(j,len(past)):
            m,v=past[k]
            if m<=remaining:
                rec(remaining-m,k,[x*y for x,y in zip(prod,v)])
    rec(n-1,0,[O]*15)
assert len(cats)==200
assert [i+1 for i,w in enumerate(first) if w is None]==[14]
print('Exactly one actual size-eight pure row (row 14), using the analytic purity for that row.')
print('Each other row has a separated normalized rooted defect, at grades',
      ','.join(str(w[0]) if w else 'pure' for w in first))
print('Across these excluded rows, the smallest certified defect magnitude is at least 2^(%d).'
      %min(x[1] for x in first if x))

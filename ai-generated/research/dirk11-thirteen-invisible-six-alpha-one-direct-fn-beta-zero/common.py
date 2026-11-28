"""Confirm exact projection intersection and copy only the true survivors."""
from pathlib import Path
from itertools import combinations
from flint import fmpz_poly
import sys
d=Path(sys.argv[1])
def factors(n):
    fs=[fmpz_poly(list(map(int,x.read_text().split())))for x in (d/n).glob('*.txt')]
    assert all(a.gcd(b).degree()==0 for a,b in combinations(fs,2))
    return fs
def prod(a):
    v=fmpz_poly([1])
    for p in a:v*=p
    return v
h,k,l=map(factors,['one-reverse','two-reverse','Jleader'])
assert list(map(lambda r:sum(x.degree()for x in r),(h,k,l)))==[408,432,24]
g=prod(h).gcd(prod(k))
assert g.degree()==84 and g.gcd(prod(l)).degree()==0
targets={(12,16227),(12,54123),(60,-1461941766456)}
common=[a for a in h if (a.degree(),int(a[0])) in targets]
assert len(common)==3 and (g//prod(common)).degree()==0
out=d/'common';out.mkdir()
for i,a in enumerate(common):
    (out/f'{i:02d}.txt').write_text(' '.join(map(str,a.coeffs()))+'\n')
print('Exact common support',[(x.degree(),int(x[0]))for x in common],
      '; gcd with the affine-leader projection is 1.')

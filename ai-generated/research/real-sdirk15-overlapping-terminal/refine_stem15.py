"""Stage stronger bounds strictly inside the original unique stem branch."""
import json
from fractions import Fraction
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
out = Path(sys.argv[1])
old = Path(sys.argv[2]) if len(sys.argv) > 2 else here.parent / 'real-sdirk15-movable-port'
old_ct = json.loads((old / 'stem-centers.json').read_text())
new_ct = json.loads((here / 'refined-stem-centers.json').read_text())
assert old_ct.keys() == new_ct.keys()
assert old_ct['clocks'].keys() == new_ct['clocks'].keys()
F = Fraction
for n, aa in old_ct['clocks'].items():
    bb = new_ct['clocks'][n]
    assert len(aa) == len(bb)
    for a, b in zip(aa,bb):
        # Allow outward rounding in the dyadic boxes.
        assert abs(F(a)-F(b)) + F('1e-245') + F(2,1<<1024) < F('1e-46')
for n in ('v','y'):
    assert abs(F(old_ct[n])-F(new_ct[n])) + F('1e-224') + F(2,1<<1024) < F('1e-29')
code = (old / 'check_stem15.py').read_text()
for a,b,n in [("'1e-46'","'1e-245'",1),("'1e-29'","'1e-224'",2)]:
    assert code.count(a) == n
    code = code.replace(a,b)
out.mkdir(parents=True, exist_ok=True)
(out / 'stem-centers.json').write_bytes((here / 'refined-stem-centers.json').read_bytes())
(out / 'check_stem15.py').write_text(code)

#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
from sys import argv
from flint import fmpq,fmpq_poly,fmpz_poly
assert len(argv)==4, 'usage: check-pair-support.py exact-cofactor exact-guards exact-initial-ledger'
D=Path(__file__).resolve().parent
readz=lambda f:fmpz_poly([int(x)for x in Path(f).read_text().split()])
C=readz(argv[1]);G=readz(argv[2])
assert sha256(Path(argv[1]).read_bytes()).hexdigest()==(D/'pair-cofactor.sha256').read_text().strip()
assert G==readz(D/'pair-guard-support.txt')
assert C.degree()==3120 and C.gcd(G)==1 and int(C.leading_coefficient())%103==18
assert G.degree()==220
assert sorted((x.degree(),m)for x,m in G.factor()[1])==[(d,1)for d in (4,4,16,24,24,28,60,60)]
S=G*fmpz_poly([-1,1])    # B=1 is not an ordinary (nonendpoint) site.
for line in Path(argv[3]).read_text().splitlines():
    w=line.split()
    i=next(i for i,x in enumerate(w)if x[0]=='-'or x[0].isdigit())
    d=fmpq_poly([fmpq(x)for x in w[i:]]).numer()
    d//=d.content()
    d//=d.gcd(d.derivative())
    q,r=divmod(S,d)
    assert r==0, (line[:100],d.degree())
print('Exact paired-gap support and every removed coefficient content checked')

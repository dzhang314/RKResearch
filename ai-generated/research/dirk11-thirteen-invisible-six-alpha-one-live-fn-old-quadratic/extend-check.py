"""Apply an exact new exceptional slice to the sibling checked clock engine."""
import hashlib, sys
from pathlib import Path
d=Path(__file__).resolve().parent
p=d.parent/'dirk11-thirteen-invisible-six-alpha-one-live-fn-carrier-slices'/'proof.py'
s=p.read_bytes()
assert hashlib.sha256(s).hexdigest()==sys.argv[1]
s=s.decode()
updates={
    'choices=["zero-carrier","ghost-fifth"]':'choices=["old-linear"]',
    "{'zero-carrier':a0,'ghost-fifth':B*zq-zp}[args.chart]":'W0[2]',
    "{'zero-carrier':ee,'ghost-fifth':H.to(B*zq-zp)}[args.chart]":'H.to(W0[2])',
    'cases={':"""cases={'old-linear':{**std,(48,1865429207937):('q',22,1),
      (60,-1461941766456):('old',22,1),(36,-7295157):('full',24,4)},""",
}
for a,b in updates.items():
    assert s.count(a)==1
    s=s.replace(a,b)
sys.argv=[str(p),'--chart','old-linear',*sys.argv[2:]]
exec(compile(s,str(p),'exec'),{'__name__':'__main__','__file__':str(p)})

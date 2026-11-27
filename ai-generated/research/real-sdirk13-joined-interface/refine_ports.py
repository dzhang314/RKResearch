"""Stage narrower boxes on the same independently certified forward branch."""
from pathlib import Path
import re,sys
here=Path(__file__).resolve().parent
old=Path(sys.argv[2]) if len(sys.argv)>2 else here.parent/'real-sdirk13-forward-ports'
source=old/'check_two_ports.py'
dst=Path(sys.argv[1]);dst.mkdir(parents=True,exist_ok=True)
base=source.read_text()
last=(here/'all-centers.txt').read_text().splitlines()
centers=[l.split()[1] for l in last if re.match(r'^[2345vzw] ',l)]
for n in re.findall(r'"([0-9]+\.[0-9]{40,})"',base):
    match=[x for x in centers if x.startswith(n[:32])]
    assert len(match)==1,n
    base=base.replace(n,match[0])
for a,b in [('B=256','B=1024'),('1e-51','1e-205'),('1e-27','1e-182'),('1e-19','1e-160')]:
    assert base.count(a)==(2 if a=='1e-27' else 1)
    base=base.replace(a,b)
(dst/'check_two_ports.py').write_text(base)

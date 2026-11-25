"""Independent additional same-fiber projection for the bare cubic coprimality question."""
from pathlib import Path
import json,sys
from math import gcd
import exact_index as EI
from check_pencil_projection import ev,interp,trim,res,cubic_pair
def run(src,dst):
 d=json.loads((dst/'exact_cubic_outer.json').read_text());R=d['R'];old=abs(int(json.loads((dst/'index_cubic.json').read_text())['raw_hex'],16))
 B=EI.bi(33,12,EI.inn)
 def pair(z):return cubic_pair(z)[1],[ev(row,z) for row in B]
 U=interp([EI.fixed(*pair(z),5,33) for z in range(292)])
 assert all(ev(U,z)==res(*pair(z),5,33) for z in [2,-1,295])
 n=EI.fixed(R,U,len(R)-1,len(U)-1);s=gcd(old,n);e=[];left=s
 for p in (2,3,5,7,11,13):
    k=0
    while not left%p:left//=p;k+=1
    e.append(k)
 print(len(U)-1,abs(n).bit_length(),s.bit_length(),left.bit_length(),e,flush=True)
 (dst/'cubic_joint_norm.json').write_text(json.dumps({'U':U,'norm':hex(n),'gcd':hex(s),'resid':hex(left),'small':e},separators=(',',':'))+'\n')
if __name__=='__main__':run(Path(sys.argv[1]),Path(sys.argv[2]))

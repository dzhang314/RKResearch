from pathlib import Path
from math import gcd
import sys,json
root=Path(sys.argv[1]);a=json.loads((root/'quartic_global_accepted.json').read_text());quad=[];S=1
for v in a:
 m=v['m'];g=v['g'];t=v['t'];u=v['u'];b=v['b']
 if len(g)==2:
    S*=m;assert b==[3,0] and (t[0]+u[0])%m==1
 else:
    c,h,_=g
    conj=lambda v:[(v[0]-h*v[1])%m,-v[1]%m]
    sub=lambda k,v:[(k-v[0])%m,-v[1]%m]
    assert conj(t)==sub(1,u) and conj(u)==sub(1,t) and conj(b)==sub(6,b)
    quad.append((m,(h*h-4*c)%m))
m,h=quad[0];n,k=quad[1];Q=m*n;disc=(h+m*((k-h)*pow(m,-1,n)%n))%Q
assert S==3478762188949
assert Q==11712161789730284342016914945454990277045396849422221142542420594260361
assert disc==8483038916109478940533923281725988412336325038253298332050421596975837 and gcd(disc,Q)==1
print('S, Q, D:',S,Q,disc)
print('All self-reflected and all conjugate-reflected components checked.')

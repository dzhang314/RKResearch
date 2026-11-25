#!/usr/bin/env python3
"""Additive exact verification of the field-independent pure leakage obstruction
and quartic supports without b, terminal, origin or amplitude assumptions."""
from fractions import Fraction
from math import gcd,prod,isqrt
from pathlib import Path
import json,sys
sys.path.insert(0,sys.argv[1])
from verify_quartic_global import S
from check_pencil_projection import F,J,D,N,ev,res,add,multiply
src,dst=map(Path,sys.argv[1:3])
assert D==[12,-44,35] and N==[210,-672,819,-460,100]
assert add(multiply([6945015,-14124306,10612140,-2835400],D),multiply([-396831,992390],N))==[5670]
assert res(D,N,2,4)==2**2*3**5*5**3*7
assert ev(N,Fraction(2,5))==Fraction(1134,25) and ev(N,Fraction(6,7))==Fraction(30,2401)
print('Pure cubic: incompatible D=N=0 in every characteristic >7, without either pencil or mesh.')
data=next(d for d in json.loads((src/'integer_ports.json').read_text()) if d['name']=='quartic')
R,T=(json.loads((dst/'exact_quartic_outer.json').read_text())[k] for k in ['R','T'])
sq=json.loads((dst/'quartic_global_accepted.json').read_text());prior={r['m'] for r in sq};extra=2551619843329
cm=[43,53,109,107451025593855819651531329774816424560049512380020377454517620130829,7109270134834058998139,104295260060968696963648183,extra,65637022433];ok=[]
s=abs(int(json.loads((dst/'index_quartic.json').read_text())['raw_hex'],16));v=abs(int(json.loads((dst/'quartic_mixed_0.json').read_text())['norm'],16));d=gcd(s,v)
for p in (2,3,5,7,11,13):
 while not d%p:d//=p
work=d;pr=1
for m in cm:
 assert d%m==0 and gcd(pr,m)==1;pr*=m
 while gcd(m,work)>1:work//=gcd(m,work)
assert work==1
for m in cm:
 V=S(m);g=[v[0] for v in V.gcd(V.ints(R),V.ints(T))];L=S(m,g);z=L.cn(-g[0]) if len(g)==2 else (0,1);zero,one=L.cn(0),L.cn(1);sub=lambda a,b:L.plus(a,L.neg(b))
 A,M,B=([L.val(L.ints(row),z) for row in p] for p in [data['A'],data['C'],data['H'][0]])
 dp=L.gcd(A,M);assert len(dp)==2;t=L.neg(dp[0]);u=L.mul(t,z)
 if m==7109270134834058998139:
    assert z==one and u==t;continue
 assert L.unit(t) and L.unit(u) and L.unit(sub(t,u)) and L.val(B,t)==zero
 f=L.val(L.ints(F),t);j=L.val(L.ints(J),t)
 if m in (43,104295260060968696963648183):
    assert f==zero and L.unit(j);continue
 assert L.unit(f) and L.unit(j);b=L.neg(L.mul(j,L.inv(f)));W=L.add(L.ints(J),L.sc(L.ints(F),b))
 assert L.unit(b) and L.val(W,t)==L.val(W,u)==zero
 Q=L.prod([L.neg(t),one],[L.neg(u),one]);H,rem=L.div(W,Q);assert not rem and len(H)==5 and L.prod(H,Q)==W
 at=L.val(H,t);au=L.val(H,u);assert L.unit(H[0]) and L.unit(at) and L.unit(au)
 def mom(k,x):return L.val([zero]*(1+k)+[L.mul(v,L.inv(L.cn(1+k+i))) for i,v in enumerate(H)],x)
 cap=L.mul(mom(2,t),L.inv(L.mul(t,j)));assert L.unit(cap) and mom(1,t)==zero
 assert sub(mom(2,u),L.mul(t,mom(1,u)))==L.mul(cap,L.mul(u,L.val(L.ints(J),u)))
 if m in (53,65637022433):assert at==au and L.plus(t,u)==one and b==L.cn(3)
 else:assert L.unit(sub(at,au)) and L.unit(sub(L.plus(t,u),one)) and L.unit(sub(b,L.cn(3)))
 if m==extra:
    assert len(g)==2 and b==L.cn(-1) and u==one and L.unit(sub(t,one))
    witness=dict(m=m,z=z[0],t=t[0],u=u[0],b=b[0],R=[v[0] for v in H],kappa=cap[0],amplitudes=[at[0],au[0]])
    assert witness==dict(m=extra,z=867363036929,t=568542283607,u=1,b=2551619843328,R=[1835664608774,2097292441940,474800605300,899778513974,1716],kappa=1822585602379,amplitudes=[497510006143,204296485046])
 else:assert L.unit(L.plus(b,one))
 ok.append(m)
assert set(ok)==prior|{extra} and extra==155773*16380373
assert all(all(p%k for k in range(2,isqrt(p)+1)) for p in (155773,16380373))
print('With no b, level-value, or pivot amplitude guards: only additional quartic component p∈{155773,16380373}, unique prime-field fixture with b=−1, u=1.')
print('Every quartic fixture has b, κ, R(0), R(t), R(u) nonzero. R(t)=R(u) iff t+u=1 iff b=3 iff p divides 3478762188949.')

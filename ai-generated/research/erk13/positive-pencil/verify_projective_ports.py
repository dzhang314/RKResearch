#!/usr/bin/env python3
"""Projective boundary [a:b]=[0:1], checked in original coordinates.
Additionally rechecks the small p=181 same-knot obstruction for the cubic."""
from fractions import Fraction as Rat
from math import gcd,lcm,isqrt,prod
from pathlib import Path
import json,sys
sys.path.insert(0,sys.argv[1])
from verify_quartic_global import S
from check_pencil_projection import F,J,D,N,res,ev,gcd_mod
src,dst=map(Path,sys.argv[1:3])
rows=json.loads((src/'integer_ports.json').read_text())
def locus(kind,m):
 d=next(d for d in rows if d['name']==kind);q=json.loads((dst/('exact_'+kind+'_outer.json')).read_text())
 V=S(m);g=[v[0] for v in V.gcd(V.ints(q['R']),V.ints(q['T']))];L=S(m,g);z=L.cn(-g[0]) if len(g)==2 else (0,1)
 A,C=([L.val(L.ints(row),z) for row in a] for a in [d['A'],d['C']]);p=L.gcd(A,C);assert len(p)==2
 return L,z,L.neg(p[0])
for m,_ in json.loads((dst/'cubic_global_components.json').read_text()):
 L,z,t=locus('cubic',m);assert L.unit(L.val(L.ints(F),t))
print('No bare noncoprime cubic for W=F: every candidate of the universal original-index support forces F(t) a unit.')
# If a full degree-five mesh existed, W=F would force N proportional to F,
# thus P(0)=0, and the branch-free representation forces z=4/5.
z=Rat(4,5);f=list(F[:-1]);fr=[c*z**i for i,c in enumerate(f)];hr=[c*(ev(D,z)*z**i+z**3*ev(N,z)) for i,c in enumerate(J)]
d=lcm(*(x.denominator for x in fr));e=lcm(*(x.denominator for x in hr));assert (d,e)==(3125,78125)
ff=[int(x*d) for x in fr];hh=[int(x*e) for x in hr]
u=res(f,ff,5,5);v=res(f,hh,5,6);assert (u,v)==(4171045098189220973568,-1090571191482582559273376244326989824)
assert gcd(u,v)==2**10*3**4*7**5*11**2*181
assert gcd_mod(f,ff,181)[0]==[100,1] and gcd_mod(f,hh,181)[0]==[80,1] and ev(hh,81,181)==75
print('The only candidate p=181 has two different forced values t=81 and t=101: no projective W=F cubic full mesh.')
# Use the original quartic projection coverage, without assuming the profile
# still has exact degree four. The contrast remains -j(t)*F(tY) here.
masses=[43,53,109,107451025593855819651531329774816424560049512380020377454517620130829,7109270134834058998139,104295260060968696963648183,2551619843329,65637022433];survive=[]
for m in masses:
 L,z,t=locus('quartic',m);u=L.mul(z,t);one=L.cn(1);zero=L.cn(0)
 if z==one:assert m==7109270134834058998139;continue
 assert L.unit(z) and L.unit(t) and L.unit(L.plus(z,L.cn(-1)))
 ft=L.val(L.ints(F),t)
 if L.unit(ft):continue
 assert m in (43,104295260060968696963648183) and ft==zero and L.d==1
 j=lambda y:L.val(L.ints(J),y);assert L.unit(j(t)) and L.val(L.ints(F),u)==zero
 Q=L.prod([L.neg(t),one],[L.neg(u),one]);R,rem=L.div(L.ints(F),Q);assert not rem and len(R)==4 and L.prod(R,Q)==L.ints(F)
 def mom(k,y):return L.val([zero]*(k+1)+[L.mul(c,L.inv(L.cn(1+k+i))) for i,c in enumerate(R)],y)
 k=L.mul(mom(2,t),L.inv(L.mul(t,j(t))));assert mom(1,t)==zero
 gap=L.plus(mom(2,u),L.neg(L.plus(L.mul(t,mom(1,u)),L.mul(k,L.mul(u,j(u))))));assert not gap[1]
 q=gcd(m,gap[0]);assert (m,q) in [(43,1),(104295260060968696963648183,2662133)]
 if q>1:
    assert all(q%v for v in range(2,isqrt(q)+1))
    w=[z[0],t[0],u[0],k[0]]+[x[0] for x in R]+[L.val(R,t)[0],L.val(R,u)[0]]
    w=[v%q for v in w];assert w==[686626,1200902,1461232,1288066,2425131,474070,2661935,132,2413436,248697]
    assert (w[1]+w[2])%q==1 and (w[-1]+w[-2])%q==0 and all(w);survive.append(q)
assert survive==[2662133]
other=2551619843329*prod(v['m'] for v in json.loads((dst/'quartic_global_accepted.json').read_text()))
assert gcd(other,2662133)==1
print('W=F: sole three-primitive factor profile in every characteristic >13 is the prime-field cubic degree-drop at p=2662133; κ and all three amplitudes nonzero.')

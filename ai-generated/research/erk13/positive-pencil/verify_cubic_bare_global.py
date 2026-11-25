#!/usr/bin/env python3
"""Exact ground-field classification of the bare cubic coprimality gate;
with or without pivot nonvanishing, terminal guard, or full deg-five mesh.
Independent integer checks at every interpolation node and enough field primes
for rigorous CRT. Each ring gcd validated by two quotients and one Bezout
identity, so un-factored integer components cover every residue prime."""
import json,sys
from math import gcd,isqrt
from pathlib import Path
sys.path.insert(0,sys.argv[1])
from verify_indices import fieldres,inner
from verify_quartic_global import S
from check_pencil_projection import F,J,ev,res,cubic_pair,interp
def main(src,dst):
 D=next(d for d in json.loads((src/'integer_ports.json').read_text()) if d['name']=='cubic')
 d=json.loads((dst/'exact_cubic_outer.json').read_text());R,T=d['R'],d['T']
 new=json.loads((dst/'cubic_joint_norm.json').read_text());U=new['U'];I=int(new['norm'],16)
 old=int(json.loads((dst/'index_cubic.json').read_text())['raw_hex'],16)
 # Explicit bidegree (33,12); C has bidegree (5,7): 7*33+12*5=291.
 assert len(U)-1<=291
 rows=[interp([inner(t,z) for t in range(34)]) for z in range(13)]
 q=[interp([row[i] if i<len(row) else 0 for row in rows]) for i in range(34)]
 for z in range(292):
    A,C=cubic_pair(z);assert A==[ev(c,z) for c in D['A']] and C==[ev(c,z) for c in D['C']]
    assert res(C,[ev(c,z) for c in q],5,33)==ev(U,z)
 B=sum(c*c for c in R)**(len(U)-1)*sum(c*c for c in U)**(len(R)-1)
 assert I and I*I<=B
 limit=1000000;tab=bytearray(b'\1')*(limit+1);tab[:2]=b'\0\0'
 for i in range(2,isqrt(limit)+1):
    if tab[i]:tab[i*i::i]=b'\0'*((limit-i*i)//i+1)
 P=1;k=0
 for p in range(limit,1,-1):
    if tab[p]:
       assert fieldres(R,U,p)==I%p;k+=1;P*=p
       if P*P>4*B:break
 assert P*P>4*B
 print('Original-q C-projection U degree',len(U)-1,'all 292 Bareiss nodes verified;',abs(I).bit_length(),'index bits certified by',k,'different prime residues.',flush=True)
 N=gcd(abs(I),abs(old));assert N==int(new['gcd'],16);small=[]
 for p in (2,3,5,7,11,13):
    e=0
    while N%p==0:N//=p;e+=1
    small.append(e)
 assert N==int(new['resid'],16) and small==new['small']
 comps=json.loads((dst/'cubic_global_components.json').read_text());assert len(comps)==4
 prod=1;left=N;rec=[]
 for m,flags in comps:
    assert N%m==0 and gcd(prod,m)==1;prod*=m
    while gcd(left,m)>1:left//=gcd(left,m)
    L=S(m);zero,one=L.cn(0),L.cn(1)
    G=L.gcd(L.ints(R),L.ints(T));assert len(G)==2;z=L.neg(G[0]);assert L.unit(z) and L.unit(L.plus(z,L.cn(-1)))
    A,C=([L.val(L.ints(row),z) for row in v] for v in [D['A'],D['C']]);h=L.gcd(A,C);assert len(h)==2;t=L.neg(h[0]);u=L.mul(t,z);assert L.unit(t)
    f=L.val(L.ints(F),t);j=L.val(L.ints(J),t);assert L.unit(f) and L.unit(j)
    b=L.neg(L.mul(j,L.inv(f)));W=L.add(L.ints(J),L.sc(L.ints(F),b))
    assert L.unit(b) and L.unit(L.plus(b,one)) and L.val(W,t)==L.val(W,u)==zero and len(W)==7 and L.unit(W[-1])
    masks=([0,12,-15],[-18,-24,60],[60,-40,-50],[-45,60])
    xp=one;F0=[]
    for row in masks:F0.append(L.mul(L.val(L.ints(row),z),L.inv(xp)));xp=L.mul(xp,t)
    assert len(F0)==4 and L.unit(F0[-1]) and L.unit(F0[0])
    def mom(i,y):return L.val([zero]*(i+1)+[L.mul(c,L.inv(L.cn(1+i+n))) for n,c in enumerate(F0)],y)
    kap=L.mul(mom(3,t),L.inv(L.mul(t,j)));assert L.unit(kap)
    assert mom(1,t)==mom(2,t)==zero and mom(2,u)==L.mul(t,mom(1,u))
    assert L.plus(mom(3,u),L.neg(L.mul(t,mom(2,u))))==L.mul(kap,L.mul(u,L.val(L.ints(J),u)))
    a1=L.val(F0,t);a2=L.val(F0,u);g=L.gcd(W,F0);gh=L.gcd([zero]+W,F0)
    assert len(g)>=2 and g==gh
    numerator,rem=L.div([zero]+W,gh);assert not rem;tail,rem=L.div(F0,gh);assert not rem and L.unit(numerator[-1]) and L.unit(tail[-1])
    assert L.prod([zero]+W,tail)==L.prod(numerator,F0)
    empirical=['accept',len(g)-1,True,True,L.unit(a1),L.unit(a2),True,3]
    assert flags==empirical
    ints=lambda xs:[c[0] for c in xs]
    rec.append(dict(m=m,z=z[0],t=t[0],u=u[0],b=b[0],P=ints(F0),kappa=kap[0],g=ints(g),N=ints(numerator),T=ints(tail),pivots=[a1[0],a2[0]]))
    print('Component',m.bit_length(),'bits, unique prime-field root; common degree',len(g)-1,'minimal numerator degree',len(numerator)-1,'nonzero pivots',L.unit(a1),L.unit(a2),flush=True)
 assert left==1 and comps[0][0]==23 and [r[1][1:2]+r[1][4:6] for r in comps]==[[2,True,False],[1,False,True],[1,True,False],[1,True,True]]
 (dst/'cubic_bare_accepted.json').write_text(json.dumps(rec,separators=(',',':'))+'\n')
 print('All candidate primes covered. Sole full mesh p=23; genuine two-amplitude full mesh impossible. Bare cubic coprimality exceptions form 4 pairwise coprime components.',flush=True)
if __name__=='__main__':main(Path(sys.argv[1]),Path(sys.argv[2]))

#!/usr/bin/env python3
"""Complete geometric finite-field fiber checks for regular asymmetric support."""
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx,nmod_mpoly_ctx,fmpz_mod_poly_ctx,fmpz_mod_mpoly_ctx
from math import isqrt
from scalar_basis import OUT as DATA
from prime_certificates import PRIMES,certify
NUMBERS=[p for p in range(11,998) if all(p%d for d in range(2,isqrt(p)+1))]
assert len(NUMBERS)==164
assert all(certify(p) for p in PRIMES)
NUMBERS += list(PRIMES)
assert len(set(NUMBERS))==169

def eval_at(basis,val,K,R):
 nm=max((i for i,j,c in basis),default=0)
 nn=max((j for i,j,c in basis),default=0)
 cs=[K.zero() for i in range(nm+1)]
 qv=[K.one()]
 for _ in range(nn):qv.append(qv[-1]*val)
 p=K.characteristic()
 for i,j,c in basis:
   m=c%p
   if m:cs[i]+=m*qv[j]
 return R(cs)
for p in NUMBERS:
 stat=[]
 for tag,parts in DATA.items():
  var=parts['var']; big=p>=2**63
  ctx=(fmpz_mod_mpoly_ctx if big else nmod_mpoly_ctx).get((var,'q'),p)
  univ=fmpz_mod_poly_ctx(p) if big else (lambda v:nmod_poly(v,p))
  ps=[ctx.from_dict({(i,j):c%p for i,j,c in e if c%p}) for e in parts['basis']]
  rs=[ps[0].resultant(f,var) for f in ps[1:]]
  r=univ([])
  for h in rs:
   if h.is_zero():continue
   assert h.degrees()[0]==0
   a=[0]*(h.degrees()[1]+1)
   for (_,j),c in h.terms():a[j]=int(c)
   r=r.gcd(univ(a))
  if r.is_zero():
   raise AssertionError(('unresolved identically zero projection',p,tag))
  counts=[]
  for fact,e in r.factor()[1]:
    d=fact.degree()
    K=fq_default_ctx(p,d,'w');R=fq_default_poly_ctx(K)
    q=R(list(map(int,fact.coeffs()))).roots()[0][0]
    guard=eval_at(parts['guard'],q,K,R)
    if guard.is_zero():
      counts.append((d,0));continue
    rc=R.zero()
    for E in parts['basis']:rc=rc.gcd(eval_at(E,q,K,R))
    if rc.is_zero():
      raise AssertionError(('all pivot rows vanish in a guarded fiber',p,tag,fact))
    while rc.degree()>0:
      g=rc.gcd(guard)
      if g.degree()<=0:break
      rc,rem=divmod(rc,g)
      assert rem.is_zero()
    counts.append((d,rc.degree()))
    assert rc.degree()==0,(p,tag,fact,q,rc)
  stat.append((tag,r.degree(),counts))
 if p in (11,13,997) or p>997:print(p,stat,flush=True)
print('complete regular geometric tests',len(NUMBERS),flush=True)

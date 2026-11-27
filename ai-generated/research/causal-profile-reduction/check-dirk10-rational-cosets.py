#!/usr/bin/env python3
"""Exact finite obstruction for fourth-power classes of rational front clocks.

The rational valuations and allowed singular exceptions are justified in the
companion manuscript. Local residue points are retained conservatively: this is
not a claim of a lift in each accepted class. Standard-library arithmetic only.
"""
from functools import cache
from pathlib import Path
from runpy import run_path
from math import gcd,isqrt,prod
from itertools import product
import sys
BASE = (Path(sys.argv[1]) if len(sys.argv)==2 else
        Path(__file__).with_name("check-dirk10-rational-clock-gates.py"))
D=run_path(str(BASE))

def mp(x,p):
 from fractions import Fraction
 x=Fraction(x)
 return x.numerator*pow(x.denominator,-1,p)%p

def choose(poly,p):
 return [x for x in range(p) if not D['ev'](poly,x)%p]
def evalraw(a,b,p):return sum(c*pow(b,j,p)for j,c in enumerate(a))%p

def local(p,want=False):
 g=gcd(4,p-1)
 cl=lambda x:pow(x%p,(p-1)//g,p)
 Q={t:choose(D['early_coeff'](t),p) for t in range(p)}
 r0={r:set()for r in range(1,p)}
 for r in r0:r0[r].add((4-r-pow(r,-1,p))%p)
 rr={t:[r for r in r0 if t in r0[r]] for t in range(p)}

 B=lambda *a:D['mul'](*a)
 A=lambda *a:D['add'](*a)
 out={}; flags={}
 unitD=lambda x:x%p
 for t in range(p):
  if not(rr[t] and Q[t]):continue
  for s in Q[t]:
   phase=''
   if p==11 and (s,t) not in {(0,6),(8,8),(9,0)}:continue
   if (s*t*(t-6)*(2*t-3))%p==0:
    phase='early singular'
   else:
    f=D['specialized']
    q=[mp(a,p)for a in D['q4'](s,t)]
    for k in range(p):
     c=[mp(a,p)for a in f(s,t,k)[:5]]
     if c[0]:continue
     _,yn,yd,wn,wd=c
     m=[mp(a,p)for a in f(s,t,k)[5]]
     if not yd and not yn or not wd and not wn:
      phase='0/0 head';break
     y=yn*pow(yd,-1,p)%p if yd else None
     w=wn*pow(wd,-1,p)%p if wd else None
     if y is None:y,w=w,y # use w only for possible pole
     phi=[1,-14,56,-84,42]
     mq=B(m,q)
     if y is None:
      c1=-mp(mq[5] if len(mq)>5 else 0,p)*pow(42,-1,p)%p
      c0=-mp((mq[4] if len(mq)>4 else 0)-c1*84,p)*pow(42,-1,p)%p
      fs=[]
     else:
      py=evalraw(phi,y,p)
      if not py:
       phase='phi pole';break
      ly=-evalraw(mq,y,p)*pow(py,-1,p)%p
      if w is None:
       c1=-mp(mq[5] if len(mq)>5 else 0,p)*pow(42,-1,p)%p
       c0=ly-c1*y
       fs=[-y,1]
      else:
       pw=evalraw(phi,w,p)
       if not pw:
        phase='phi pole';break
       if y==w:
        py1=evalraw([j*a for j,a in enumerate(phi)if j],y,p)
        m1=evalraw([j*a for j,a in enumerate(mq)if j],y,p)
        c1=(-m1-ly*py1)*pow(py,-1,p)%p
       else:
        lw=-evalraw(mq,w,p)*pow(pw,-1,p)%p
        c1=(ly-lw)*pow(y-w,-1,p)%p
       c0=ly-c1*y
       fs=B([-y,1],[-w,1])
     sf=A(mq,B(phi,[c0,c1]));sf=D['trim'](x%p for x in sf)
     if not sf:
      phase='zero quintic';break
     if fs:
      sf,rem=D['divrem'](sf,fs)
      assert all(not mp(a,p)for a in rem)
      sf=D['trim'](mp(x,p) for x in sf)
     if D['split_mod'](sf,p):
      phase='split';break
   if phase:
    flags[s,t]=phase
    for r in rr[t]:
     a=cl(r)
     b=cl(5*t-3) if (5*t-3)%p else cl(28*pow(9,-1,p))
     out.setdefault((a,b),set()).add((s,t))
 inf=any(D['split_mod'](v,p) for v in (D['REGULAR'],D['EXCEPTIONAL']))
 if inf:
  s,t=0,p
  out[cl(-140),cl(pow(28,-1,p))]=out.get((cl(-140),cl(pow(28,-1,p))),set())|{('inf',)}
  out[cl(-pow(140,-1,p)),cl(pow(28,-1,p))]=out.get((cl(-pow(140,-1,p)),cl(pow(28,-1,p))),set())|{('inf',)}
 if want:print(p,out,flags,flush=True)
 return set(out)

def prime(p):return p>1 and all(p%t for t in range(2,isqrt(p)+1))


DATA=[(420,4,0),(-1008,3,0),(1008,2,0),(-504,1,0),(108,0,0),
      (-168,2,1),(252,1,1),(-108,0,1),(33,0,2),(-28,1,2),(-3,0,3)]

def val(x,p):
 n=0
 while x%p==0:
  x//=p;n+=1
 return n,x

@cache
def early_pole(p,d,T):
 if d>=21:
  a,c=val(420,p);b,k=val(-3,p)
  return (3*d+a-b)%4==0 and any((c*S**4+k*T**3)%p==0 for S in range(1,p))
 terms=[(*val(c,p),i,j) for c,i,j in DATA]
 for vs in range(-4*d-10,4*d+11):
  lo=min(a+i*vs-j*d for a,c,i,j in terms)
  ls=[(c,i,j) for a,c,i,j in terms if a+i*vs-j*d==lo]
  if len(ls)==1:continue
  if any(not sum(c*S**i*T**j for c,i,j in ls)%p for S in range(1,p)):return True
 return False

@cache
def exceptional(a,b,p):
 va,A=val(a,p);vb,B=val(b,p)
 g=gcd(4,p-1)
 def eq(v,u):
  return (v-vb)%4==0 and (u-B)%16==0 if p==2 else (v-vb)%4==0 and pow(u%p,(p-1)//g,p)==pow(B%p,(p-1)//g,p)
 for sign in (1,-1): # positive valuation or negative valuation of ratio
  for d in range(1,25):
   if (sign*d-va)%4:continue
   if p==2:
    T=(4*2**d-(2**(2*d)*A+pow(A,-1,16) if sign==1 else A+2**(2*d)*pow(A,-1,16)))%16
    if early_pole(p,d,T%p) and eq(-d,5*T-3*2**d):return True
   else:
    T=(-pow(A,-1,p) if sign==1 else -A)%p
    if not early_pole(p,d,T):continue
    if p!=5 and eq(-d,5*T):return True
    if p==5 and d>=2 and eq(1-d,T):return True
    if p==5 and d==1 and (T==3 or eq(0,T-3)):return True
 if va%4==0:
  if p==2:
   t=(4-A-pow(A,-1,16))%16
   if eq(0,5*t-3):return True
  else:
   t=(4-A-pow(A,-1,p))%p
   if (5*t-3)%p:
    if eq(0,5*t-3):return True
   elif p==3:
    if eq(2,2) or eq(3,1):return True
   elif p==7:
    if eq(1,1):return True
   else:
    assert False
 return False



def verify_negative_29():
    p=29
    cl=lambda a:pow(a%p,7,p)
    assert not any(D['split_mod'](a,p)for a in (D['REGULAR'],D['EXCEPTIONAL']))
    pairs=[]
    for s,t in product(range(p),repeat=2):
        if D['ev'](D['early_coeff'](t),s)%p:
            continue
        delta=5*t-3 if (5*t-3)%p else 28*pow(9,-1,p)
        if cl(delta)!=cl(27):
            continue
        roots=[u for u in range(1,p)if cl(u)==cl(-1) and
               (4-u-pow(u,-1,p)-t)%p==0]
        if roots:pairs.append((s,t,roots))
    assert pairs==[(0,6,[28]),(14,6,[28])]
    simple,finite,pole=([-56,324,-567,308],[-14,76,-124,63],[-40,220,-371,196])
    assert not any(D['split_mod'](c,p)for c in (simple,finite,pole))
    q0=D['mul']([1,-1],[84*row[0]+row[3]for row in D['MOMENT_INV']])
    mq=D['mul']([336,-168],q0)
    phi=D['PHI']; PH=lambda x:evalraw(phi,x,p)
    qs=choose([112,-39,8],p)
    assert qs==[10,13]
    for k in qs:
        yD,wD=(84*k-3136)%p,mp(28*k-D['Q'](3136,5),p)
        yN,wN=(168*k-756)%p,mp(D['Q'](112,5)*k,p)
        y,w=yN*pow(yD,-1,p)%p,wN*pow(wD,-1,p)%p
        ly,lw=-evalraw(mq,y,p)*pow(PH(y),-1,p)%p,-evalraw(mq,w,p)*pow(PH(w),-1,p)%p
        slope=(ly-lw)*pow(y-w,-1,p)%p
        num=D['trim'](c%p for c in D['add'](mq,D['mul'](phi,[ly-slope*y,slope])))
        q,rem=D['divrem'](num,D['mul']([-y,1],[-w,1]))
        assert all(not mp(c,p)for c in rem)
        got=[mp(c,p)for c in q]
        assert got==([25,20,8,19] if k==10 else [24,27,27,18])
        assert not D['split_mod'](got,p)
    print("q=29 excludes the full negative fourth-power coset")


def run_sieve():
    vals=[sign*prod(p**j for p,j in zip((2,3,5,7),exps))
          for sign in (-1,1) for exps in product(range(4),repeat=4)]
    pair=[(a,b) for a in vals for b in vals]
    assert len(set(pair))==262144
    ps=[11,13,17,19,29,31,37,41,53,61,67,73,79,83,89,97,101,109,113,137,149,157,173,181,193]
    assert all(map(prime,ps))
    for p in ps:
        tab=local(p)
        g=gcd(4,p-1)
        cs={a:pow(a%p,(p-1)//g,p)for a in vals}
        pair=[(a,b)for a,b in pair if (cs[a],cs[b])in tab]
    assert len(pair)==66
    totals=[]
    for p in (2,3,5,7):
        pair=[(a,b)for a,b in pair if exceptional(a,b,p)]
        totals.append(len(pair))
    assert totals==[8,8,3,3]
    assert pair==[(-1,27),(3,27),(27,27)]
    print("262144 initial pairs; 66 good-prime survivors; small-prime survivors",totals)
    print("only 5t-3=27*fourth; a/b in (-1,3,27)*fourth")
    # Valuation-only table for the oriented positive representative R=3*fourth.
    for p in (2,3,5,7):
        a,R=val(3,p)
        pole=[]
        for sgn,d in product((-1,1),range(1,25)):
            if (sgn*d-a)%4:
                continue
            tp=(-R if sgn<0 else -pow(R,-1,p))%p
            if early_pole(p,d,tp):
                pole.append(sgn*d)
        assert pole==([-3,1] if p==3 else [])


if __name__=="__main__":
    run_sieve()
    verify_negative_29()

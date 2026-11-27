#!/usr/bin/env python3
"""Regenerate every generated Lean data/receipt module of the real DIRK10 endpoint.

By default compare against the checked-in modules, without editing them.
With --out DIRECTORY, write the generated modules into that directory.
Uses only Python's standard library and the sibling exact quotient replay.
"""
import argparse
from fractions import Fraction as Q
import json
from math import lcm, prod
from pathlib import Path
import runpy
import tempfile


def build_flags(repo):
    D=runpy.run_path(str(repo/'check-dirk10-real-algebraic.py'))
    J=json.loads((repo/'dirk-order10-eleven-real-coefficients.json').read_text())
    F,E,Q=D['V'],D['E'],D['Q']
    def decode(x,alg):
     if alg is None:return Q(int(x[0]),int(x[1]))
     cs=[decode(y,alg.base) for y in x]
     while cs and not cs[-1]:cs.pop()
     return E(alg,tuple(cs))
    A=[list(map(lambda u:decode(u,F), row))for row in J['matrix_lower_triangular']]
    b=[decode(w,F)for w in J['weights']]
    c=[decode(w,F)for w in J['nodes']]
    def matv(v):return tuple(sum(a*x for a,x in zip(row,v))for row in A)
    def dot(a,v):return sum(x*y for x,y in zip(a,v))
    def cp(u,v):return tuple(x*y for x,y in zip(u,v))
    g=tuple(F.cast(Q(4,3)) if i==1 else F.zero for i in range(11))
    kap=D['xi']**2/(3*(D['a']-D['xi'])*(2*D['b']-D['a']))
    h=tuple(kap*D['ev'](D['H'],x)/D['ev'](D['M'],x) if 2<=i<10 else F.zero for i,x in enumerate(c))
    T=tuple(D['ev'](D['integral'](D['H']),x) for x in c)
    C=cp(c,h); C2=cp(c,C)
    bands=[[],[],[],[g],[g,h],[g,h,C],[g,h,C,C2,T]]
    for d in range(7,10):
     k=10-d
     pivot=tuple(range(11-k,11))
     vs=[]
     for i in range(11-k):
        v=[F.zero]*11
        v[i]=F.one
        for j in pivot:
           v[j]=-b[i]*prod((c[i]-c[l])/(c[j]-c[l]) for l in pivot if l!=j)/b[j]
        for n in range(k):assert not dot(b,cp(v,[x**n for x in c]))
        vs.append(tuple(v))
     bands.append(vs)

    def witness(y, d):
     V=bands[d];n=len(V)
     if d>=7:sol=list(y[:n])
     else:
        piv={}
        for p in range(11):
           row=[v[p]for v in V];out=y[p]
           for k in range(n):
              coef=row[k]
              if not coef:continue
              if k in piv:
                 w,t=piv[k];out-=coef*t
                 row=[s-coef*v for s,v in zip(row,w)]
              else:
                 piv[k]=([x/coef for x in row],out/coef)
                 break
           else:assert not out,(d,p)
        assert len(piv)==n
        sol=[F.zero]*n
        for j in range(n-1,-1,-1):
           v,t=piv[j]
           sol[j]=t-sum(v[k]*sol[k]for k in range(j+1,n))
     assert all(y[p]==F.cast(sum(w*v[p]for w,v in zip(sol,V))) for p in range(11))
     return sol
    AS=[ [witness(matv(v),d+1)for v in bands[d]]for d in range(9)]
    CS=[ [witness(cp(c,v),d+1)for v in bands[d]]for d in range(9)]
    MS=[[[[witness(cp(v,w),d+e)for w in bands[e]]for v in bands[d]]
         if d+e<10 else []for e in range(10)]for d in range(10)]
    Ps=[]
    for d in range(9):
     out=tuple((d+1)*a0-b0 for a0,b0 in zip(matv([x**d for x in c]),[x**(d+1)for x in c]))
     Ps.append(witness(out,d+1))
    assert not any(dot(b,v)for V in bands for v in V)
    qs=[(d+1)*dot(b,[x**d for x in c]) for d in range(10)]
    assert qs==[F.one]*10

    pool=[];ids={}
    def obj(x):
     x=F.cast(x)
     if x not in ids:ids[x]=len(pool);pool.append(x)
     return ids[x]
    assert obj(0)==0 and obj(1)==1
    A0=[[obj(x)for x in row]for row in A]
    B0=[obj(x)for x in b];C0=[obj(x)for x in c]
    Bs=[[[obj(x)for x in v]for v in V]for V in bands]
    MsA=[[[obj(x)for x in v]for v in M]for M in AS]
    MsC=[[[obj(x)for x in v]for v in M]for M in CS]
    Ms=[[[[[obj(x)for x in row]for row in L]for L in M]for M in Q]for Q in MS]
    PS=[[obj(x)for x in w]for w in Ps]
    def rept(p,alg):
     if alg is None:
        p=Q(p);return [str(p.numerator),str(p.denominator)]
     q=alg.cast(p)
     return [rept(q.c[i]if i<len(q.c)else alg.down(0),alg.base)for i in range(len(alg.mod)-1)]
    data={'coef':[rept(x,F)for x in pool],'A':A0,'b':B0,'c':C0,'bs':Bs,'Astep':MsA,'Cstep':MsC,'mulstep':Ms,'prim':PS,
     'starInv':rept(1/(11*dot(b,[x**10 for x in c])-1),F),
     'shape':[len(v)for v in bands]}
    print('exact finite flags for all generator instances PASS; pool entries',len(pool),'flag dims',data['shape'],flush=True)
    return data


def generate_data(J, q):
    def rat(x):return Q(int(x[0]),int(x[1]))
    sx=25
    sy=lcm(*[(rat(x)/sx**i).denominator for row in q['mod_r8'][:-1] for i,x in enumerate(row)])

    def coeffs(s,j=0,l=0):return [rat(x)/sx**i/sy**(j+l)for i,x in enumerate(s)]
    def mid(s,l=0):return [coeffs(x,j,l)for j,x in enumerate(s)]
    def top(s):return [mid(x,l)for l,x in enumerate(s)]
    def leaves(s):
     if isinstance(s,list):
       for r in s:yield from leaves(r)
     else:yield s
    def transform(s,f):
     if isinstance(s,list):return [transform(x,f)for x in s]
     return f(s)
    def scmul(s,m):
     k=transform(s,lambda x:x*m)
     assert all(x.denominator==1 for x in leaves(k))
     return transform(k,int)
    def er(x):
     if isinstance(x,int):
        s=str(x)
        return '('+s+')' if x<0 else s
     return '('+','.join(map(er,x))+')'
    def ar(x):
     if isinstance(x,int):return str(x)
     return '#['+','.join(map(ar,x))+']'
    i0=[-rat(x)*sx**(3-j) for j,x in enumerate(q['mod_k'][:-1])]
    assert all(x.denominator==1 for x in i0)
    i0=[int(x)for x in i0]
    i1=[scmul(coeffs(x),-sy**(3-j)) for j,x in enumerate(q['mod_r8'][:-1])]
    i2=[scmul(mid(x),-sy**(2-j)) for j,x in enumerate(q['mod_r9'][:-1])]

    vals=[top(q)for q in J['coef']]
    approxDen={}
    def denom(s):
     k=tuple(leaves(s))
     if k not in approxDen:approxDen[k]=lcm(*(x.denominator for x in k))
     return approxDen[k]
    denoms=[1]; denomids={1:0}; pool=[(scmul(vals[0],1),0),(scmul(vals[1],1),0)]; ids={}
    def encode(i,D):
     if i in (0,1):return i
     if D not in denomids:denomids[D]=len(denoms);denoms.append(D)
     key=(i,D)
     if key not in ids:
      ids[key]=len(pool);pool.append((scmul(vals[i],D),denomids[D]))
     return ids[key]
    def group(g):
     D=lcm(*(denom(vals[i])for i in leaves(g)))
     return transform(g,lambda i:encode(i,D))
    meta={'mA2':('A',2),'mB1':('b',1),'mC1':('c',1),'size1':('shape',1),
          'basis3':('bs',3),'moveA3':('Astep',3),'moveC3':('Cstep',3),'moveP5':('mulstep',5),'prim2':('prim',2)}
    st={}
    for name,(key,k) in meta.items():
      if k==3:
        st[name]=[group(v)for v in J[key]]
      elif k>=4:
        st[name]=[[group(u)for u in v]for v in J[key]]
      else:
        st[name]=J[key]if name=='size1' else group(J[key])
    inv=top(J['starInv'])
    di=denom(inv); sl=er(scmul(inv,di))
    print('root scale suffix digits',len(str(sy)),'global max denom digits',max(map(lambda a:len(str(a)),denoms)),'pack count',len(pool),flush=True)

    n=16
    s=['''module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagReplayCore

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerData
open DIRKRealIntegerFlagReplay CubicCubicQuadraticFractionReplay
open CubicCubicQuadraticReplay (Reductions)

''']
    s+=['def rootScaleY : Nat := '+str(sy)+'\n']
    s+=['def denominatorPred : Array Nat := '+ar([u-1 for u in denoms])+'\n\n']
    for i in range(0,len(pool),n):
     pairs=['⟨'+er(x)+', denominatorPred.getD '+str(j)+' 0⟩'for x,j in pool[i:i+n]]
     s+=['def pool_'+str(i//n)+' : Array C18 := #[\n  '+',\n  '.join(pairs)+'\n]\n\n']
    s+=['def coeff (i : Nat) : C18 :=\n  match i/'+str(n)+' with\n']
    s += ['  | '+str(k)+' => pool_'+str(k)+'.getD (i%'+str(n)+') (pack 0)\n'for k in range((len(pool)+n-1)//n)]
    s+=['  | _ => pack 0\n\n']
    s+=['def reductions : Reductions := {\n  inner := '+er(i0)+'\n  middle := '+er(i1)+'\n  outer := '+er(i2)+' }\n\n']
    for name,(_,k) in meta.items():
     typ='Nat'
     for _ in range(k): typ='Array ('+typ+')'
     s+=['def '+name+' : '+typ+' := '+ar(st[name])+'\n\n']
    s+=['''def get1 (v : Array Nat) (i : Nat) : Nat := v.getD i 0
def get2 (v : Array (Array Nat)) (i j : Nat) := get1 (v.getD i #[]) j
def get3 (v : Array (Array (Array Nat))) (i j k : Nat) := get2 (v.getD i #[]) j k
def get5 (v : Array (Array (Array (Array (Array Nat))))) (a b c d e : Nat) :=
  get3 ((v.getD a #[]).getD b #[]) c d e

def packet : Packet where
  red := reductions
  a i j := coeff (get2 mA2 i j)
  b i := coeff (get1 mB1 i)
  clock i := coeff (get1 mC1 i)
  size := get1 size1
  basis d i j := coeff (get3 basis3 d i j)
  nextA d i k := coeff (get3 moveA3 d i k)
  nextC d i k := coeff (get3 moveC3 d i k)
  product d e i j k := coeff (get5 moveP5 d e i j k)
  primitive d k := coeff (get2 prim2 d k)
  bushInverse := ⟨''',sl,', ',str(di-1),'⟩\n\nend RKResearch.Certified.DIRKRealOrderTenIntegerData\n']
    return ''.join(s)


def generate_checks(L):
    tpl='''module

{imports}

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
'''
    def mk(name,s,*imps):
     if not imps:imps=('DIRKRealIntegerFlagData',)
     (L/(name+'.lean')).write_text(tpl.format(imports='\n'.join('public import RKCert.ReviewedNative.'+x for x in imps))+s+'\nend RKResearch.Certified.DIRKRealOrderTenIntegerChecks\n')
    mk('DIRKRealIntegerFlagCheckBlocks','''
def blockA (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkA packet d)
def blockC (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkC packet d)
def blockS (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkSilent packet d)
def blockP (d e : Nat) : Bool := (List.finRange (packet.size d)).all fun i =>
  (List.finRange (packet.size e)).all (checkProduct packet d e i)
''')
    base='DIRKRealIntegerFlagCheckBlocks'
    files=[]
    def gauges(name,exprs):
     files.append(name);mk(name, '\n'.join('theorem '+nm+' : '+v+' = true := by decide +kernel' for nm,v in exprs),base)
    gauges('DIRKRealIntegerFlagCheckBase', [('chk_node','checkNode packet'),('chk_bush','checkBush packet')])
    for k in ('A','C','S'):
     n=10 if k=='S' else 9
     for j in range(0,n,3):
        gauges('DIRKRealIntegerFlagCheck'+k+str(j), [('chk_'+k+str(i),'block'+k+' '+str(i))for i in range(j,min(j+3,n))])
    for j in range(0,10,3):
     cases=[('chk_Q'+str(i),f'checkScalar packet {i}')for i in range(j,min(j+3,10))]
     cases.extend([('chk_P'+str(i),f'checkPrimitive packet {i}') for i in range(j,min(j+3,9))])
     gauges('DIRKRealIntegerFlagCheckMoments'+str(j),cases)
    for d in range(10):
     gauges('DIRKRealIntegerFlagCheckProducts'+str(d),
        [('chk_m'+str(d)+'_'+str(e),f'blockP {d} {e}')for e in range(10-d)])
    g=''
    for k,n in [('A',9),('C',9),('S',10)]:
     g+=f'theorem ar{k} (d : Nat) (hd : d < {n}) : block{k} d = true := by\n  interval_cases d\n'
     g+=''.join(f'  · exact chk_{k}{j}\n'for j in range(n))+'\n'
    g+='''theorem arp (d e : Nat) (h : d+e < 10) : blockP d e = true := by
  have hn : d < 10 := by omega
  interval_cases d
'''
    for d in range(10):
     g+='  · have he : e < '+str(10-d)+' := by omega\n    interval_cases e\n'
     g+=''.join(f'    · exact chk_m{d}_{e}\n'for e in range(10-d))
    g+='''
theorem arPrim (d : Nat) (hd : d < 9) : checkPrimitive packet d = true := by
  interval_cases d
'''+''.join(f'  · exact chk_P{i}\n'for i in range(9))+'''
theorem arScalar (d : Nat) (hd : d < 10) : checkScalar packet d = true := by
  interval_cases d
'''+''.join(f'  · exact chk_Q{i}\n'for i in range(10))+'''
theorem receipts : Receipts packet := by
  refine ⟨chk_node,?_,?_,?_,arPrim,?_,arScalar,chk_bush⟩
  · intro d hd i
    exact List.all_eq_true.mp (arA d hd) i (List.mem_finRange i)
  · intro d hd i
    exact List.all_eq_true.mp (arC d hd) i (List.mem_finRange i)
  · intro d e hd i j
    exact List.all_eq_true.mp
      (List.all_eq_true.mp (arp d e hd) i (List.mem_finRange i)) j (List.mem_finRange j)
  · intro d hd i
    exact List.all_eq_true.mp (arS d hd) i (List.mem_finRange i)

end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
'''
    coreimp='\n'.join('public import RKCert.ReviewedNative.'+x for x in files)
    p=tpl.format(imports=coreimp+'\nimport Mathlib.Tactic.IntervalCases')
    (L/'DIRKRealIntegerFlagReceipts.lean').write_text(p+g)


def split_high_advances(L):
    base='''module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks
{imps}

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks

open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
'''
    mods=[]
    dims={6:5,7:8,8:9}
    for d,sz in dims.items():
     for start in range(0,sz,2):
        m=f'DIRKRealIntegerFlagCheckA{d}From{start}';mods.append(m)
        src=base.format(imps='')
        for i in range(start,min(sz,start+2)):
          src+=f'theorem chk_A{d}i{i} : checkA packet {d} ⟨{i}, by decide +kernel⟩ = true := by decide +kernel\n'
        (L/(m+'.lean')).write_text(src+'\nend RKResearch.Certified.DIRKRealOrderTenIntegerChecks\n')
    src=base.format(imps='\n'.join('public import RKCert.ReviewedNative.'+m for m in mods)+'\nimport Mathlib.Tactic.FinCases')
    for d,sz in dims.items():
     src+=f'''theorem chk_A{d} : blockA {d} = true := by
  apply List.all_eq_true.mpr
  intro i _
  have he : packet.size {d} = {sz} := by decide +kernel
  obtain ⟨j, hj⟩ : ∃ j : Fin {sz}, Fin.cast he.symm j = i :=
    ⟨Fin.cast he i, Fin.ext rfl⟩
  rw [←hj]
  fin_cases j
'''
     src+=''.join(f'  · exact chk_A{d}i{i}\n'for i in range(sz))
    (L/'DIRKRealIntegerFlagCheckA6.lean').write_text(src+'\nend RKResearch.Certified.DIRKRealOrderTenIntegerChecks\n')


def generate_roots(p,L):
    cf=[list(map(lambda l:Q(int(l[0]),int(l[1])),s))for s in p['mod_r8']]
    def fmt(a):
     if a.denominator==1:
        return str(a.numerator)
     return '(mkRat ('+str(a.numerator)+') '+str(a.denominator)+')'
    pref='''module

public import RKCert.ReviewedNative.DIRKRealRootParameters
public import RKCert.ReviewedNative.PolynomialBracket
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact real specialization of the degree-18 replay data using
strict rational sign changes. No approximation of an algebraic node
enters the proof. -/
namespace RKResearch.Certified.DIRKRealOrderTenRoots
open DIRKRealOrderTenData CubicCubicQuadraticRatReplay
open CubicCubicQuadraticReplay (v2 v3)
open RKCert.ReviewedNative.PolynomialBracket

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem realMap (x : ℚ) : (algebraMap ℚ ℝ) x = (x : ℝ) := rfl

noncomputable def innerCoeffs : List ℝ := [1314/125, -87/125, -4/5, 1]

noncomputable def suffix (x : ℝ) : List ℝ :=
  [-val3 x reductions.middle.1, -val3 x reductions.middle.2.1,
   -val3 x reductions.middle.2.2,1]

theorem inner_eval (x : ℝ) :
    horner innerCoeffs x = x^3 - val3 x reductions.inner := by
  norm_num [innerCoeffs, horner, val3, v3, reductions, realMap, Rat.mkRat_eq_div]
  ring

theorem suffix_eval (x y : ℝ) :
    horner (suffix x) y = y^3 - val9 x y reductions.middle := by
  simp only [suffix,horner,val9,v3,add_zero,mul_zero]
  ring

theorem horner_neg (cs : List ℝ) (x : ℝ) :
    horner (cs.map Neg.neg) x = -(horner cs x) := by
  induction cs with
  | nil => simp [horner]
  | cons a cs ih => simp only [List.map_cons,horner,ih]; ring

theorem exists_inner :
    ∃ x ∈ Set.Ioo (-204748/100000 : ℝ) (-204747/100000),
      x^3=val3 x reductions.inner := by
  obtain ⟨x,hx,hx0⟩ := exists_real_horner_root
    (lo := (-204748/100000 : ℝ)) (hi := (-204747/100000 : ℝ))
    (B:=3) (by norm_num) (by norm_num) (by norm_num) innerCoeffs
    (by norm_num [innerCoeffs,horner]) (by norm_num [innerCoeffs,horner])
  exact ⟨x,hx,sub_eq_zero.mp ((inner_eval x).symm.trans hx0)⟩
'''
    s=[pref]
    for ep,label,sgn in [(6377,'loleft',-1),(6380,'lowright',1),(8664,'midleft',1),(8668,'midright',-1)]:
     x=Q(ep,10**4)
     a=[sum(rr[j]*x**n for n,rr in enumerate(cf))*(-1)**j*sgn for j in range(3)]
     b='['+','.join(map(fmt,a))+']'
     rhs=('-' if sgn<0 else '')+f'(horner (suffix x) ({ep}/10000))'
     out=f'horner (suffix x) ({ep}/10000) < 0' if sgn<0 else f'0 < horner (suffix x) ({ep}/10000)'
     s+=[f'''
def sign_{label} : List ℚ := {b}

theorem suffix_sign_{label} {{x : ℝ}}
    (hx : x ∈ Set.Ioo (-204748/100000 : ℝ) (-204747/100000)) :
    {out} := by
  have hL : (204747/100000 : ℝ) ≤ -x := by
    have hh := hx.2
    norm_num at hh ⊢
    linarith
  have hU : -x ≤ (204748/100000 : ℝ) := by
    have hh := hx.1
    norm_num at hh ⊢
    linarith
  have hPos := horner_pos_of_box
    (lo := (204747/100000 : ℚ)) (hi := (204748/100000 : ℚ))
    (x := -x) (by norm_num) (by simpa using hL) (by simpa using hU)
    sign_{label} (by decide +kernel)
  have eq : horner (sign_{label}.map (Rat.castHom ℝ)) (-x) = {rhs} := by
    norm_num [sign_{label}, suffix, horner, val3, v3, reductions, realMap,
      Rat.mkRat_eq_div]
    ring
  rw [eq] at hPos
  linarith only [hPos]
''']
    s+=[r'''
theorem exists_suffix_pair {x : ℝ}
    (hx : x ∈ Set.Ioo (-204748/100000 : ℝ) (-204747/100000)) :
    ∃ y z : ℝ, y ∈ Set.Ioo (6377/10000) (6380/10000) ∧
      z ∈ Set.Ioo (8664/10000) (8668/10000) ∧
      horner (suffix x) y=0 ∧ horner (suffix x) z=0 := by
  obtain ⟨y,hy,hy0⟩ := exists_real_horner_root
    (lo := (6377/10000 : ℝ)) (hi := (6380/10000 : ℝ))
    (B:=2) (by norm_num) (by norm_num) (by norm_num) (suffix x)
    (suffix_sign_loleft hx) (suffix_sign_lowright hx)
  obtain ⟨z,hz,hz0⟩ := exists_real_horner_root
    (lo := (8664/10000 : ℝ)) (hi := (8668/10000 : ℝ))
    (B:=2) (by norm_num) (by norm_num) (by norm_num) ((suffix x).map Neg.neg)
    (by rw [horner_neg]; linarith only [suffix_sign_midleft hx])
    (by rw [horner_neg]; linarith only [suffix_sign_midright hx])
  rw [horner_neg,neg_eq_zero] at hz0
  exact ⟨y,z,hy,hz,hy0,hz0⟩

theorem outer_eval (x y z : ℝ) :
    (z-y)*(z^2-val x y z reductions.outer) =
      horner (suffix x) z - horner (suffix x) y := by
  norm_num [val,v2,val9,val3,v3,suffix,horner,reductions,realMap,Rat.mkRat_eq_div]
  ring

theorem exists_roots : ∃ x y z : ℝ, Roots reductions x y z := by
  obtain ⟨x,hx,hx0⟩ := exists_inner
  obtain ⟨y,z,hy,hz,hy0,hz0⟩ := exists_suffix_pair hx
  have hne : z-y ≠ 0 := by
    have hy0 := hy.2
    have hz0 := hz.1
    intro eq
    linarith only [hy0,hz0,eq]
  have h2 := outer_eval x y z
  rw [hy0,hz0,sub_self] at h2
  exact ⟨x,y,z,⟨hx0,sub_eq_zero.mp ((suffix_eval x y).symm.trans hy0),
    sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hne)⟩⟩

end RKResearch.Certified.DIRKRealOrderTenRoots

#print axioms RKResearch.Certified.DIRKRealOrderTenRoots.exists_roots
''']
    (L/'DIRKRealFlagRoots.lean').write_text(''.join(s))


def root_parameters(q):
    def neg(x):
        if isinstance(x[0], str):
            return [str(-int(x[0])), x[1]]
        return [neg(v) for v in x]
    def emit(x):
        if isinstance(x[0], str):
            n,d = x
            if n == '0':
                return '0'
            if n.startswith('-'):
                n = '(' + n + ')'
            return n if d == '1' else '(mkRat ' + n + ' ' + d + ')'
        return '(' + ','.join(map(emit,x)) + ')'
    leading = '''module

public import RKCert.ReviewedNative.CubicCubicQuadraticRatReplay

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenData
open CubicCubicQuadraticRatReplay

def reductions : Reductions := {
'''
    for name,key in [('inner','mod_k'),('middle','mod_r8'),('outer','mod_r9')]:
        leading += '  ' + name + ' := ' + emit(list(map(neg,q[key][:-1])))
        leading += ' }\n\n' if name == 'outer' else '\n'
    return leading + 'end RKResearch.Certified.DIRKRealOrderTenData\n'


def generate(repo, out):
    q=json.loads((repo/'dirk-order10-eleven-real-coefficients.json').read_text())
    J=build_flags(repo)
    out.mkdir(parents=True,exist_ok=True)
    (out/'DIRKRealIntegerFlagData.lean').write_text(generate_data(J,q))
    (out/'DIRKRealRootParameters.lean').write_text(root_parameters(q))
    generate_roots(q,out)
    generate_checks(out)
    split_high_advances(out)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,help='write modules here instead of comparing')
    args=parser.parse_args()
    repo=Path(__file__).resolve().parent
    if args.out:
        generate(repo,args.out)
        return
    original=repo.parents[1]/'lean'/'RKCert'/'ReviewedNative'
    with tempfile.TemporaryDirectory() as tmp:
        target=Path(tmp)
        generate(repo,target)
        mismatch=[x.name for x in sorted(target.glob('*.lean')) if x.read_bytes() != (original/x.name).read_bytes()]
        assert not mismatch, mismatch
        print('Regenerated Lean modules match all checked-in generated sources byte for byte.')


if __name__=='__main__':
    main()

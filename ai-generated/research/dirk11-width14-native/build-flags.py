#!/usr/bin/env python3
"""Integer four-quadratic flag receipts from the frozen exact width-14 literal.

Python is a witness generator, not a proof dependency.  Lean checks the
multiplications and flags, including the scaled tree defect, independently.
"""
from fractions import Fraction as Q
from math import lcm, prod
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
DEFAULT_LITERAL = HERE.parent / 'dirk11-width14-real-reflected-shell' / 'tableau.json'
DEFAULT_REPLAY = DEFAULT_LITERAL.with_name('replay.py')
parser=argparse.ArgumentParser()
parser.add_argument('--literal',type=Path,default=DEFAULT_LITERAL)
parser.add_argument('--replay',type=Path,default=DEFAULT_REPLAY)
parser.add_argument('--lean',type=Path,default=HERE.parent.parent/'lean/RKCert/ReviewedNative')
x=parser.parse_args()
# Import the exact algebra arithmetic, never the seed or order checker.
s=x.replay.read_text().split('# Scalar geometry.')[0]
D={}
exec(compile(s,str(x.replay),'exec'),D)
Alg,E=D['Alg'],D['E']
J=json.loads(x.literal.read_text()); assert J['width']==14 and J['order']==11

def decode(v,alg):
    if alg is None:return Q(v)
    assert len(v)==2
    return E(alg,tuple(D['trim'](decode(i,alg.base) for i in v)))
F=None
for i,s in enumerate(J['relations']):F=Alg(F,[decode(v,F)for v in s], 'coefficient '+str(i+1))

def encode(v,alg=F):
    if alg is None:return Q(v)
    v=alg.cast(v)
    return tuple(encode(v.c[i]if i<len(v.c)else alg.down(0),alg.base)for i in range(2))

def dot(u,v):return F.cast(sum(a*b for a,b in zip(u,v)if a and b))
def matv(v):return tuple(dot(row,v)for row in A)
def cp(u,v):return tuple(a*b for a,b in zip(u,v))
def scal(k,v):return tuple(k*a for a in v)
def sub(u,v):return tuple(a-b for a,b in zip(u,v))
A=[tuple(decode(v,F)for v in row)+(F.zero,)*(14-len(row))for row in J['A']]
b=tuple(decode(v,F)for v in J['b']); c=tuple(sum(row)for row in A)
assert len(A)==14 and not any(A[i][j]for i in range(14)for j in range(i+1,14))
assert all(sum(row)==row[0]for i,row in enumerate(A)if i==0)
Z,O=F.zero,F.one

class RREF:
    def __init__(self):self.p={}
    def extend(self,v):
        v=list(v)
        for p,q in sorted(self.p.items()):
            if v[p]:v=list(sub(v,scal(v[p],q)))
        i=next((i for i,z in enumerate(v)if z),None)
        if i is None:return
        v=tuple(a/v[i]for a in v); assert v[i]==O
        for p,q in list(self.p.items()):
            if q[i]:self.p[p]=sub(q,scal(q[i],v))
        self.p[i]=v
    def keys(self):return sorted(self.p)
    def basis(self):return [self.p[k]for k in self.keys()]
    def witness(self,v):
        q=[v[k]for k in self.keys()]
        assert all(dot(q,w)==z for w,z in zip(zip(*self.basis()),v)) if q else not any(v)
        return q

C=[tuple(v**d for v in c)for d in range(13)]
prim=[sub(scal(d+1,matv(C[d])),C[d+1])for d in range(10)]
B=[RREF()]
for d in range(1,8):
    r=RREF(); B.append(r)
    for v in B[d-1].basis():
        r.extend(v); r.extend(matv(v)); r.extend(cp(c,v))
    r.extend(prim[d-1]);
    for a in range(1,d//2+1):
        for u in B[a].basis():
            for v in B[d-a].basis():r.extend(cp(u,v))
    print('grade',d,'actual defect rank',len(r.p),flush=True)
for d in range(8,11):
    k=11-d; pivot=tuple(range(14-k,14)); r=RREF()
    assert len(set(c[j]for j in pivot))==k and all(b[j]for j in pivot)
    for i in range(14-k):
        v=[Z]*14; v[i]=O
        for j in pivot:
            v[j]=-b[i]*prod((c[i]-c[l])/(c[j]-c[l])for l in pivot if l!=j)/b[j]
        # The pivot coordinates are the identity, so this is already RREF.
        r.p[i]=tuple(v)
    B.append(r)
    print('grade',d,'paid moment superspace rank',len(r.p),flush=True)
for d,r in enumerate(B):
    assert all(not dot(b,v)for v in r.basis()),d
assert all((d+1)*dot(b,C[d])==O for d in range(11))

# Rescale the radicals themselves so that the polynomial reductions use only
# integers.  This introduces no division inside any Lean arithmetic receipt.
def leaves(v):
    if isinstance(v,tuple):
        for z in v:yield from leaves(z)
    else:yield v

def content(v,k):
    if isinstance(v,tuple):return tuple(content(z,k)for z in v)
    return v*k

def adjusted(v,sc):
    if not sc:return v
    return tuple(content(adjusted(q,sc[:-1]),Q(1,sc[-1]**i))for i,q in enumerate(v))

scales=[];red=[]
for j,t in enumerate(J['relations']):
    def norm(v):
        if j==0:return Q(v)
        return tuple(norm1(z,j-1)for z in v)
    def norm1(v,k):return Q(v)if k==0 else tuple(norm1(z,k-1)for z in v)
    words=[adjusted(content(norm(v),-1),scales)for v in t[:2]]
    s=lcm(*(q.denominator for w in words for q in leaves(w)))
    red.extend([content(words[0],s*s),content(words[1],s)] if j==3 else [content(words[0],s*s)])
    if j<3:assert not any(leaves(words[1]))
    scales.append(s)
assert all(q.denominator==1 for w in red for q in leaves(w))

def coords(v):return adjusted(encode(v),scales)
def den(v):return lcm(*(q.denominator for q in leaves(v)))
def denV(v):return lcm(*(den(coords(q))for q in v))
D0=lcm(*(denV(v)for v in A+[b,c]))
print('root scales',scales,'common A/b denominator digits',len(str(D0)),flush=True)
scB=[[denV(v)for v in r.basis()]for r in B]
Bnum=[ [scal(s,v)for s,v in zip(sc,r.basis())]for sc,r in zip(scB,B)]

def witness(v,d):
    coeff=[z/s for z,s in zip(B[d].witness(v),scB[d])]
    assert all(dot(coeff,w)==z for w,z in zip(zip(*Bnum[d]),v))if coeff else not any(v)
    K=denV(coeff)
    return K,[coords(z*K)for z in coeff]

def po(d):return witness(scal(D0**(d+1),prim[d]),d+1)
ma=[ [witness(scal(D0,matv(v)),d+1)for v in Bnum[d]]for d in range(10)]
mc=[ [witness(scal(D0,cp(c,v)),d+1)for v in Bnum[d]]for d in range(10)]
mp=[[[[witness(cp(v,w),d+e)for w in Bnum[e]]for v in Bnum[d]]if d+e<11 else []
     for e in range(11)]for d in range(11)]
pi=[po(d)for d in range(10)]
# The frozen next tree has four leaves and one seven-vertex bush at its root.
fail=84*dot(b,cp(C[4],matv(C[6])))-1
assert fail==decode(J['scaled_failure'],F)
inv=decode(J['scaled_failure_inverse'],F)/D0**12
assert fail*D0**12*inv==O
invD=den(coords(inv)); invN=coords(inv*invD)

stem='DIRK11Width14Integer'

def qshape(v):
    if isinstance(v,tuple):return '('+','.join(map(qshape,v))+')'
    assert int(v)==v
    return str(int(v))

def arr(v):return '#['+','.join(map(str,v))+']'

cache={};pool=[]
def code(z):
    if z not in cache:cache[z]=len(pool);pool.append(z)
    return cache[z]
assert code(coords(Z))==0;assert code(coords(O))==1

def arr2(v):return arr(arr(a)for a in v)
def arr3(v):return arr(arr2(a)for a in v)
def encq(w):
    s,vs=w
    return '⟨'+str(s-1)+', '+arr(code(q)for q in vs)+'⟩'

a=arr2([code(coords(v*D0))for v in row]for row in A)
w=arr(code(coords(v*D0))for v in b)
n=arr(code(coords(v*D0))for v in c)
band=arr3([[code(coords(v))for v in row]for row in bs]for bs in Bnum)
sa=arr2([encq(v)for v in band]for band in ma)
cs=arr2([encq(v)for v in band]for band in mc)
prodS=arr(arr(arr2([encq(v)for v in col]for col in group)for group in d)for d in mp)
pr=arr(encq(v)for v in pi)
print('encoded pool',len(pool),'grade dimensions',[len(q.p)for q in B],flush=True)
head='''module

public import RKCert.ReviewedNative.DIRK11Width14IntegerCore

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerData
open QuadTowerIntReplay DIRK11Width14IntegerCore
'''
head+='def reductions : Reductions := ⟨'+','.join(map(qshape,red))+'⟩\n'
head+='def denominatorPred : Nat := '+str(D0-1)+'\n'
head+='def rootScales : List Nat := ['+','.join(map(str,scales))+']\n'
# Chunking large arrays keeps kernel and elaborator depth under control.
chunk=16
for i in range(0,len(pool),chunk):
    head+='def p'+str(i//chunk)+' : Array C16 := #[\n  '+',\n  '.join(map(qshape,pool[i:i+chunk]))+'\n]\n'
head+='def coeff (i : Nat) : C16 :=\n  match i/'+str(chunk)+' with\n'
head+=''.join(f'  | {j} => p{j}.getD (i%{chunk}) (pack 0)\n'for j in range((len(pool)+chunk-1)//chunk))
head+='  | _ => pack 0\n'
head+=f'''def a : Array (Array Nat) := {a}
def b : Array Nat := {w}
def c : Array Nat := {n}
def sizes : Array Nat := {arr(len(q.p)for q in B)}
def bands : Array (Array (Array Nat)) := {band}
def stepA : Array (Array IndexWitness) := {sa}
def stepC : Array (Array IndexWitness) := {cs}
def prodW : Array (Array (Array (Array IndexWitness))) := {prodS}
def primW : Array IndexWitness := {pr}
def failureInv : C16 := {qshape(invN)}
def failureDenPred : Nat := {invD-1}

def getN (a : Array Nat) (i : Nat) : C16 := coeff (a.getD i 0)
def getW (x : IndexWitness) : Witness := ⟨x.scalePred, getN x.coefficients⟩
def emptyW : IndexWitness := ⟨0,#[]⟩
def packet : Packet where
  red := reductions
  denominatorPred := denominatorPred
  a i j := getN (a.getD i #[]) j
  b := getN b
  clock := getN c
  size d := sizes.getD d 0
  basis d i := getN ((bands.getD d #[]).getD i #[])
  nextA d i := getW ((stepA.getD d #[]).getD i emptyW)
  nextC d i := getW ((stepC.getD d #[]).getD i emptyW)
  product d e i j := getW ((((prodW.getD d #[]).getD e #[]).getD i #[]).getD j emptyW)
  primitive d := getW (primW.getD d emptyW)
  failureInverse := failureInv
  failureDenPred := failureDenPred

end RKResearch.Certified.DIRK11Width14IntegerData
'''
x.lean.mkdir(parents=True,exist_ok=True)
(x.lean/(stem+'Data.lean')).write_text(head)

# Mathematically redundant cache: the kernel checks the multiplication
# recurrence against the literal nodes, then rewrites the checked powers
# before deciding expensive matrix reads. This prevents repeated reduction
# of high nested products within every coefficient.
s='''module

public import RKCert.ReviewedNative.DIRK11Width14IntegerData

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerData
open QuadTowerIntReplay DIRK11Width14IntegerCore
'''
pt=[]
for d in range(11):
    vals=[qshape(coords((D0**d)*c0))for c0 in C[d]]
    tag=f'powRow{d}'
    s+=f'def {tag} : Array C16 := #[\n  '+',\n  '.join(vals)+'\n]\n'
    pt.append(tag)
s+='def litPow (d : Nat) (i : Fin 14) : C16 :=\n  match d with\n'
s+=''.join(f'  | {k} => {a}.getD i.val (pack 0)\n'for k,a in enumerate(pt))
s+='  | _ => pack 0\n\nend RKResearch.Certified.DIRK11Width14IntegerData\n'
(x.lean/(stem+'PowData.lean')).write_text(s)

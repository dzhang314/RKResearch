#!/usr/bin/env python3
"""Generate small untrusted normalized-vector receipts checked by Lean's kernel."""
from argparse import ArgumentParser
from pathlib import Path
from math import ceil
import json
N='ERK10SixteenF17'
NS='RKResearch.Certified.'+N
ax='RKCert.ReviewedNative.'
def ar(a):return '#['+', '.join(map(str,a))+']'
def arr(a):return '#[\n  '+',\n  '.join(map(ar,a))+' ]'

def cache(A,b):
 V=[(1,)*16];W=[tuple(sum(r)%17 for r in A)]
 G=[1];cuts=[0,1];J={}
 for n in range(2,11):
  lut={}
  for i in range(cuts[-1]):
   for k in range(cuts[n-G[i]-1],cuts[n-G[i]]):
    v=tuple(a*b%17 for a,b in zip(V[i],W[k]))
    if v not in lut:
     lut[v]=len(V); V.append(v);G.append(n)
     if n<10:W.append(tuple(n*sum(a*b for a,b in zip(r,v))%17 for r in A))
    J[i,k]=lut[v]
  cuts.append(len(V))
 assert all(g*sum(w*a for w,a in zip(b,v))%17==1 for g,v in zip(G,V))
 return V,W,G,cuts,J

def main(source,out,mods):
 data=json.loads(source.read_text());assert data['field']==17
 A=[tuple(map(int,r))for r in data['A']];b=tuple(map(int,data['b']))
 V,W,G,cuts,J=cache(A,b)
 print('Normalized profiles',[y-x for x,y in zip(cuts,cuts[1:])],
       'total',len(V),'actions',len(W),'joins',len(J))
 def write(mod,imports,body,extra=''):
  s='module\n\n'+'\n'.join('public import '+ax+i for i in imports)+extra
  s+='\n\n@[expose] public section\n\nnamespace '+NS
  s+='\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 40000\n'
  s+='\n'+body+'\n\nend '+NS+'\n'
  (out/(mod+'.lean')).write_text(s)
 def bucket(k,T):
  return '\n'.join(f'  | {i//k} => '+arr(T[i:i+k])for i in range(0,len(T),k))+'\n  | _ => #[]'
 body=f"""abbrev Count := {len(V)}
abbrev ActCount := {len(W)}
def gradeTable : Array ℕ := {ar(G)}
def cuts : Array ℕ := {ar(cuts)}
def aRows : Array (Array ℕ) := {arr(A)}
def bRow : Array ℕ := {ar(b)}
def joins : Array (Array ℕ) := {arr([[J[i,j]for j in range(cuts[10-G[i]])]for i in range(len(W))])}

def vBuckets : ℕ → Array (Array ℕ)
{bucket(16,V)}
def wBuckets : ℕ → Array (Array ℕ)
{bucket(16,W)}
"""
 write(N+'Data',[],body,'\npublic import Mathlib.Algebra.Field.ZMod')
 runs=[N+'Data',N+'Core']
 names=[]
 end=[]
 # Long first rows are split, avoiding repeated evaluation in a large proof.
 exact_rows=[]
 for i in range(cuts[5]):
  length=cuts[10-G[i]]
  for j in range(0,length,24):
   lab=f'{N}Join{i}At{j}'
   point=min(24,length-j)
   write(lab,[N+'Core'],
     f'theorem join{i}At{j} : joinSlice (tag {i}) {j} {point} = true := by decide +kernel')
   runs.append(lab);exact_rows.append(lab)
 # Construct one lightweight receipt extraction for each early row.
 join_rows=[]
 for i in range(cuts[5]):
  length=cuts[10-G[i]]
  ja=list(range(0,length,24))
  deps=[f'{N}Join{i}At{j}'for j in ja]
  lab=f'{N}Join{i}'
  body=f'theorem join{i} : joinOK (tag {i}) = true := by\n'
  body+=f'  apply finishJoin (by decide +kernel : cut (10-grade (tag {i})) = {length})\n'
  body+=f'  have H0 := join{i}At0\n'
  for k,j in enumerate(ja[1:],1):body+=f'  have H{k} := glueJoin H{k-1} join{i}At{j}\n'
  body+=f'  exact H{len(ja)-1}\n'
  write(lab,deps,body)
  join_rows.append(lab);runs.append(lab)
 for tag,lim,step,width in (('Grade',len(V),64,4),('Join',len(W),8,4),('Act',len(W),10,3),('Pay',len(V),24,4)):
  name=tag.lower()+'OK'
  key='ActCount' if tag in ('Act','Join') else 'Count'
  blocks=ceil(lim/step)
  for i in range(0,blocks,width):
   deps=[N+'Core']
   lab=f'{N}Checks{tag}{i}'
   lines=[]
   for k in range(i,min(blocks,i+width)):
    line=f'theorem block{tag}{k} : block {name} {key} {k} {step} = true := by'
    if tag=='Join' and k*step<cuts[5]:
     js=list(range(k*step,(k+1)*step))
     deps.extend(join_rows[j]for j in js if j<cuts[5])
     ts=', '.join(f'tag {j}'for j in js)
     line+=f'\n  change ([{ts}].all joinOK) = true\n'
     for j in js:
      if j>=cuts[5]:line+=f'  have join{j} : joinOK (tag {j}) = true := by decide +kernel\n'
     line+='  simp only [List.all_cons,List.all_nil,Bool.and_self,'+','.join(f'join{j}'for j in js)+']'
    else:line+=' decide +kernel'
    lines.append(line)
   write(lab,deps,'\n\n'.join(lines))
   names.append(lab);runs.append(lab)
  end.append(f'theorem all{tag} (i : ℕ) (hi : i<{blocks}) : block {name} {key} i {step}=true := by\n'
      +'  interval_cases i\n'+'\n'.join(f'  · exact block{tag}{j}'for j in range(blocks)))
 end.append('''theorem receipts : Receipts where
  grade i := block_covers (by decide) (by decide) allGrade i i.isLt
  join i hi := block_covers (by decide) (by decide) allJoin i hi
  act i hi := block_covers (by decide) (by decide) allAct i hi
  pay i := block_covers (by decide) (by decide) allPay i i.isLt''')
 write(N+'Checks',names,'\n\n'.join(end),'\nimport Mathlib.Tactic.IntervalCases')
 runs.append(N+'Checks');runs.append(N)
 mods.write_text('\n'.join(runs)+'\n')
if __name__=='__main__':
 p=ArgumentParser()
 p.add_argument('--source',type=Path,default=Path(__file__).with_name('tableau.json'))
 p.add_argument('--emit',type=Path,required=True)
 p.add_argument('--modules',type=Path,required=True)
 q=p.parse_args();main(q.source,q.emit,q.modules)

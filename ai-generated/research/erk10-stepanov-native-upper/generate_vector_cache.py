#!/usr/bin/env python3
"""Generate a smaller proof by equality classes of normalized stage vectors."""
from generate import (DEFAULT_SOURCE, MODULE, ZERO, add, arr, dot, fmt_c8, mul,
                      pack, read_method, scale, write)
from collections import Counter
from math import gcd
from pathlib import Path
import argparse


def vectors(A, b, D, p):
    # V_t = forest(t)*Phi(t,A). W_t = |t|*A*V_t. In the binary reviewed
    # constructor, V_(t ◂ u) = V_t * W_u componentwise.
    V = [(pack(1),)*15]
    W = [tuple(dot(row, V[0]) for row in A)]
    G = [1]
    cuts = [0,1]
    join = {}
    for n in range(2,p+1):
        idx = {}
        for i, ni in enumerate(G[:cuts[-1]]):
            for j in range(cuts[n-ni-1],cuts[n-ni]):
                v = tuple(mul(a,b) for a,b in zip(V[i],W[j]))
                if v not in idx:
                    idx[v] = len(V)
                    V.append(v)
                    G.append(n)
                    if n<p:
                        W.append(tuple(scale(n,dot(row,v)) for row in A))
                join[i,j] = idx[v]
        cuts.append(len(V))
    assert len(V)==582 and len(W)==274
    for v,n in zip(V,G):
        assert scale(n,dot(b,v))==pack(D**n)
    print('Normalized stage classes:',dict(Counter(G)))
    print('Number of compatible joins:',len(join))
    return V,W,G,cuts,join


def literal(a):
    if not any(a[1:]):
        return f'pack ({a[0]})'
    g = gcd(*a)
    if g>1:
        return f'content {g} {fmt_c8(tuple(x//g for x in a))}'
    return fmt_c8(a)


def cache(emit, name, vecs):
    # Deduplicate individual coordinates within each independently imported
    # block to keep this evaluated-integer fixture compact.
    deps=[]
    for first in range(0,len(vecs),64):
        k=first//64
        blk=vecs[first:first+64]
        vals=list(dict.fromkeys(x for v in blk for x in v))
        assert all(isinstance(a,int) for xs in vals for a in xs)
        IDs={x:j for j,x in enumerate(vals)}
        atomWidth=16
        idxdef = '\n'.join(
            f'  | {i//atomWidth} => '+arr(map(literal,vals[i:i+atomWidth]))
            for i in range(0,len(vals),atomWidth)
        )
        index_array=arr(arr(str(IDs[x]) for x in v) for v in blk)
        small=f"def {name}Atom{k} : ℕ → Array C8\n{idxdef}\n  | _ => #[]"
        small+=f"\ndef {name}Index{k} : Array (Array ℕ) := {index_array}"
        small+=f"""
def {name}Row{k} (offset s : ℕ) : C8 :=
  let v := (({name}Index{k}[offset]!)[s]!)
  ({name}Atom{k} (v / {atomWidth}))[v % {atomWidth}]!
"""
        nm=f"ERK10Stepanov{name}Cache{k}"
        write(emit,nm,[MODULE+"ERK10StepanovLiterals"],small)
        deps.append(nm)
    return deps


def emit_tables(emit,A,b,D,V,W,G,cuts,join):
    deps = cache(emit,"Profile",V)+cache(emit,"Action",W)
    body = f"""abbrev ClassCount := {len(V)}
abbrev ActionCount := {len(W)}
def ctag (i : ℕ) : Fin ClassCount := ⟨i % ClassCount,Nat.mod_lt _ (by decide)⟩
def gradeTable : Array ℕ := {arr(map(str,G))}
def classCut (n : ℕ) : ℕ := ({arr(map(str,cuts))}:Array ℕ)[n]!
def cgrade (i : Fin ClassCount) : ℕ := gradeTable[i.val]!
"""
    dense = [[join[i,j] for j in range(cuts[10-G[i]])] for i in range(cuts[-2])]
    body += 'def classJoins : Array (Array ℕ) := #[\n  '+",\n  ".join(arr(map(str,row)) for row in dense)+" ]\n"
    body += '''
def cjoin (i j : Fin ClassCount) : Fin ClassCount := ctag ((classJoins[i.val]!)[j.val]!)
'''
    for name,data,target in [('Profile',V,'cprofile'),('Action',W,'caction')]:
        body += f'def {target} (i : Fin ClassCount) (j : Fin 15) : C8 :=\n'
        body += '  match i.val / 64 with\n'
        for n in range((len(data)+63)//64):
            body+=f'  | {n} => {name}Row{n} (i.val % 64) j.val\n'
        body+='  | _ => pack 0\n'
    body += 'def aSupportArray : Array (List ℕ) := '+arr(str([i for i,x in enumerate(row) if x!=ZERO]) for row in A)+'\n'
    body += f'def bSupportList : List ℕ := {[i for i,x in enumerate(b) if x!=ZERO]}\n'
    body += '''
def aSupport (i : Fin 15) : List (Fin 15) := (aSupportArray[i.val]!).map (fun j => ⟨j%15,Nat.mod_lt _ (by decide)⟩)
def bSupport : List (Fin 15) := bSupportList.map (fun j => ⟨j%15,Nat.mod_lt _ (by decide)⟩)
'''
    write(emit,"ERK10StepanovClassData",[MODULE+src for src in deps],body)
    print('Cache modules:',*deps)


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--source',type=Path,default=DEFAULT_SOURCE)
    parser.add_argument('--emit',type=Path,required=True)
    args=parser.parse_args()
    D,c,b,A=read_method(args.source)
    emit_tables(args.emit,A,b,D,*vectors(A,b,D,10))

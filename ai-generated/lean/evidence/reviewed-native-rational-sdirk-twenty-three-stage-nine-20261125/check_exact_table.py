#!/usr/bin/env python3
"""Exact, standalone mathematical replay of the admitted 23-stage rational p9 witness.

This checks tree identities, not a Lean object, proof term, import closure, or axiom output.
Use --lean-root to read the two frozen Lean data files without duplicating a JSON literal,
--table for the one frozen portable JSON, or both to require exact source agreement.
"""
from argparse import ArgumentParser
from ast import literal_eval
from fractions import Fraction
from functools import cache
from hashlib import sha256
from math import factorial, prod
from pathlib import Path
import json
import re
import sys

N, P, PASSIVE = 23, 9, 11
TABLE_SHA = '4609b8fb82d606542ef596a82d35b521ae12fac992b6fc8d2ff851b5d19ac1c9'
DATA_SHA = 'f704bf83a61b7b4d555d747ff5b7bd16fae94bb1951189acbd183390b2764aae'
CORE_SHA = 'aea859426e4c32356eec86112b912ece5015ded2747dff39f639c504d1ca1ec8'
COUNTS = (1, 1, 2, 5, 14, 42, 132, 429, 1430)
TALL = Fraction(672263002006281827534440264169, 2489086143060781104997013158963200000)

def need(h, why):
    if not h:
        raise ValueError(why)

def readpin(path, expected):
    b=path.read_bytes()
    need(sha256(b).hexdigest()==expected, f'exact source fingerprint differs: {path}')
    return b.decode('utf-8')

def integer(source, name):
    m=re.search(fr'^def {name} : ℤ := (-?[0-9]+)$', source, re.M)
    need(m is not None, f'missing exact numeral {name}')
    return int(m[1])

def dense(row, cols):
    need(isinstance(row,list) and all(isinstance(x,tuple) and len(x)==2 and
          type(x[0]) is int and type(x[1]) is int and 0<=x[0]<cols and x[1]!=0
          for x in row), 'invalid sparse literal row')
    rr=dict(row)
    need(len(rr)==len(row), 'duplicate index in sparse literal row')
    return [rr.get(i,0) for i in range(cols)]

def lookup(source, name, size, width):
    sig=f'def {name} (i : Fin {size}) : Row {width} :='
    need(source.count(sig)==1, f'missing selector {name}')
    raw=source.split(sig,1)[1].split('\n\n',1)[0]
    pattern=r'if i\.val < ([0-9]+) then|\belse\b|(\[[^\r\n]+\])'
    need(not re.sub(pattern,'',raw).strip(), f'unrecognized selector syntax: {name}')
    tokens=iter(re.findall(pattern,raw))
    def node():
        cond,row=next(tokens,('', ''))
        if row:
            cells=dense(literal_eval(row),width)
            return lambda i: cells
        need(bool(cond), 'malformed row selector condition')
        left=node()
        need(next(tokens,None)==('',''), 'malformed row selector else branch')
        right=node()
        return lambda i: left(i) if i<int(cond) else right(i)
    root=node()
    need(next(tokens,None) is None, 'unconsumed selector text')
    return [root(i) for i in range(size)]

def from_lean(root):
    src=root/'RKCert/ReviewedNative'
    data=readpin(src/'RationalStrictSDIRKTwentyThreeStageNineData.lean',DATA_SHA)
    core=readpin(src/'RationalStrictSDIRKQ5CompressedCore.lean',CORE_SHA)
    d,e,diag,m=(integer(data,k) for k in ('stageScale','weightScale','diagonalInt','coreMultiplier'))
    need(d==m*integer(core,'physicalScale')==9*diag, 'signed scale/core relation')
    top=lookup(core,'normalizedRows',PASSIVE,PASSIVE)
    tail=lookup(data,'suffixRows',N-PASSIVE,N)
    a=[[m*z for z in row]+[0]*(N-PASSIVE) for row in top]+tail
    w=re.search(r'^def weightRow : Row 23 := (\[[^\r\n]+\])$',data,re.M)
    need(w is not None, 'missing weight row')
    return a,dense(literal_eval(w[1]),N),d,e

def from_table(path):
    j=json.loads(readpin(path,TABLE_SHA))
    need((j['stages'],j['order'],j['passive_core_rows'])==(N,P,PASSIVE), 'tableau domain')
    need(j['gamma']=={'num':1,'den':9}, 'literal diagonal metadata')
    tw=j['next_tall_weight']
    need(Fraction(tw['num'],tw['den'])==TALL, 'literal tall metadata')
    return j['a_integer'],j['b_integer'],j['a_denominator'],j['b_denominator']

@cache
def forests(size):
    # A tree is the ordered list of children of its root, and a leaf is ().
    # Every nonempty ordered forest is determined uniquely by first tree and tail.
    if size==0:
        return ((),)
    return tuple((first,)+tail for i in range(1,size+1)
                 for first in forests(i-1) for tail in forests(size-i))

@cache
def order(t):
    return 1+sum(map(order,t))

@cache
def tree_factorial(t):
    return order(t)*prod(map(tree_factorial,t))

@cache
def unordered_key(t):
    return tuple(sorted(map(unordered_key,t)))

def replay(a,w,d,e):
    need(len(a)==len(w)==N and all(len(row)==N for row in a), 'coefficient shape')
    need(type(d) is int and type(e) is int and d>0 and e>0, 'positive integer scales')
    need(all(type(z) is int for row in a for z in row) and all(type(z) is int for z in w), 'integer entries')
    need(all(9*row[i]==d and all(z==0 for z in row[i+1:]) for i,row in enumerate(a)),
         'not lower triangular with common nonzero rational diagonal 1/9')
    need(w[:PASSIVE]==[0]*PASSIVE and all(z>0 for z in w[PASSIVE:]), 'frozen passive/active weight profile')
    rows=[tuple((j,z) for j,z in enumerate(row) if z) for row in a]
    weights=tuple((j,z) for j,z in enumerate(w) if z)
    def action(v):
        return tuple(sum(z*v[j] for j,z in row) for row in rows)
    def out(v):
        return sum(z*v[j] for j,z in weights)
    @cache
    def stage(t):
        result=(1,)*N
        # Homogeneous integer stage vector for native Φ, following the ordered children.
        for child in t:
            result=tuple(x*y for x,y in zip(result,act_stage(child),strict=True))
        return result
    @cache
    def act_stage(t):
        return action(stage(t))
    cases=[]
    for n,k in enumerate(COUNTS,1):
        ts=forests(n-1)
        need(len(ts)==len(set(ts))==k and all(order(t)==n for t in ts), f'wrong native coverage at order {n}')
        rhs=e*d**(n-1)
        for idx,t in enumerate(ts):
            need(tree_factorial(t)*out(stage(t))==rhs, f'failed order {n}, ordered tree {idx}: {t}')
        cases.append((n,k,len(set(map(unordered_key,ts)))))
    need(sum(r[1] for r in cases)==2056 and sum(r[2] for r in cases)==486, 'total tree coverage')
    vec=(1,)*N
    for _ in range(P):
        vec=action(vec)
    tall=Fraction(out(vec),e*d**P)
    need(tall==TALL and tall!=Fraction(1,factorial(P+1)), 'missing exact order-ten tall obstruction')
    return {'kind':'exact mathematical rational replay, NOT Lean kernel/axiom verification',
            'stages':N,'common_diagonal':'1/9','has_order':P,'not_order':P+1,
            'ordered_native_conditions':2056,'unordered_classes_for_accounting_only':486,
            'order_ordered_count_unordered_count':cases,'a_integer_entries':N*N,
            'nonzero_sparse_a_entries':sum(map(len,rows)),'weights':N,
            'tenth_tall_weight':str(tall),'required_tenth_tall_weight':str(Fraction(1,factorial(P+1)))}

def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('--lean-root',type=Path)
    p.add_argument('--table',type=Path)
    opts=p.parse_args()
    if opts.lean_root is None and opts.table is None:
        p.error('provide --lean-root, --table, or both')
    try:
        a=from_lean(opts.lean_root) if opts.lean_root else None
        b=from_table(opts.table) if opts.table else None
        if a is not None and b is not None:
            need(a==b,'Lean literals versus portable JSON mismatch')
        res=replay(*(a if a is not None else b))
        res['checked_input_paths_mode']='source + table exact agreement' if a is not None and b is not None else (
            'source literals only' if a is not None else 'portable literal only')
        print(json.dumps(res,indent=2))
    except (ValueError, KeyError, TypeError, OSError) as e:
        print(f'rejected: {e}',file=sys.stderr)
        return 1
    return 0

if __name__=='__main__':
    sys.exit(main())

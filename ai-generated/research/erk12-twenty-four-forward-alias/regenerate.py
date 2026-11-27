#!/usr/bin/env python3
"""Reconstruct the 24-stage tableau by an exact paid forward-row alias.
No optimization, external solver, or numerical inputs are needed."""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import cache
from hashlib import sha256
from math import lcm, prod
from pathlib import Path
from types import ModuleType
import json
import sys

HERE=Path(__file__).resolve().parent
HASH={
    'construct.py':'74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7',
    'weighted_regular.py':'f0ab1a5026113602e6402ccf5bd5e6c1cd199e918ea285a74ebd16eb06d91571',
}
Z,O=F(0),F(1)
REC=json.loads((HERE/'transport.json').read_text())
XI,A0,R0=(F(REC[k]) for k in ('xi','a','r'))
W={F(a):F(b) for a,b in REC['W'].items()}

def module(src,path,name):
    m=ModuleType(name)
    m.__file__=str(path)
    exec(compile(src,str(path),'exec'),m.__dict__)
    return m

def checked(root,name):
    raw=(root/name).read_bytes()
    assert sha256(raw).hexdigest()==HASH[name],name
    return raw.decode()

def prepare(rk,order,vv,mul,add,scale,cardinal):
    assert order==12
    z,o=rk.Z,rk.O
    f,fo0,fr0=rk.short(5)
    more=rk.prepend((fo0,fr0),[F(2,3),F(3,4)],f)
    fp=fo0[:3]+fo0[4:]+more[0]
    fr=fr0[:3]+fr0[4:]+more[1]
    f=[[XI*u for u in row]for row in f]
    fo=[(lambda j,g=g:XI**j*g(j))for g in fp]
    centers=[z,F(1,3),F(1,2)]
    ew=[1/((1-x*x)**2*prod(x*x-y*y for y in centers if y!=x)) for x in centers]
    pin=lambda q:sum(w*vv(q,XI*(1+x)-1)for x,w in zip(centers,ew))
    a,r=A0,R0
    x=2*r*r*(2*r-1)/3
    y=-r*r*(2*r-1)*(6*r-7)/6
    k=r*r*(r-1)*(2*r-1)
    j=r*r*(1-r)/a
    reverse=[[],[a],[F(1,2)-1/(8*a),1/(8*a)],
             [-1+1/(2*a),-1/(2*a),F(2)],
             [F(1,6),z,F(2,3),F(1,6)],[r-j-x-y-k,j,x,y,k]]
    k3=16*r*r*(1-r)**2;k4=2*r*r*(r-1)*(2*r-1)
    R=lambda p:vv(p,2*r-1)-k3*vv(p,z)-k4*vv(p,o)
    Rop=lambda k:r**k-k3*F(1,2)**k-k4
    Rrow=[z,z,-k3,-k4,z,o]
    ro=[rk.eval_at(z),rk.eval_at(o),rk.moment(0),Rop]
    rr=[rk.basis(0,6),rk.basis(4,6),[F(1,6),z,F(2,3),F(1,6),z,z],Rrow]
    fixed={F(-1),F(1),1-2*XI}
    available=sorted(1-2*x for x in W)
    late=list(map(F,REC['late']))
    pure=sorted(set(late)|fixed)
    assert {2*sum(row)-1 for row in reverse}<=set(pure)
    early=sorted(set(available)-set(pure))
    assert (len(pure),len(early),len(late))==(8,3,5)
    print('Scaled forward, rough reverse, mixed reverse:',XI,a,r)
    print('Early sites:',tuple(map(str,early)),'late:',tuple(map(str,late)))
    return (f,fo,fr,6,pin,[z]*8+ew,list(zip(fo[:2],fr[:2])),
            reverse,ro,rr,4,[o,z,-o],[R],list(zip(ro[:2],rr[:2]))+[(Rop,Rrow)],
            available,[],early,late,F(0))

def patched(s):
    changes=[
      ('def build(rk, seed, order, verify_reads=False):',
       'CAP={}\n\ndef build(rk, seed, order, verify_reads=False):'),
      ('beta = [o]*(base_n+len(split))+[weight[a] for a in early]',
       'beta = [weight[-o]]+[o]*(base_n+len(split)-1)+[weight[a] for a in early]\n'
       '    assert rk.unit(beta[0]) and beta[0]==F(75625,979776)'),
      ('l += [r.copy() for r in l[:base_n+len(split)]]',
       'l += [r.copy() for r in l[1:base_n+len(split)]]'),
      ('beta += [-o]*(base_n+len(split))',
       'beta += [-o]*(base_n+len(split)-1)'),
      ('l += [probe(a) for a in pure]',
       'pure_active = [a for a in pure if a != -o]\n    l += [probe(a) for a in pure_active]'),
      ('beta += [weight[a] for a in pure]',
       'beta += [weight[a] for a in pure_active]'),
      ('forward_factor = [o,-o] if order in (15,16) else h',
       'forward_factor = [2*rk.XI-1,2-2*rk.XI,F(-1)]'),
      ('primal = beta[rev_h]*coeff',
       'primal = beta[rev_h]*coeff/(beta[rev_j] if rev_j<base_n+len(split) else o)'),
      ('assert len(out)=={11:23,12:26,13:30,14:33,15:40,16:45,17:53,18:60,19:66,20:72}[order]',
       'assert len(out)==25, len(out)\n    CAP.update(locals())'),
      ('pure_start = live+base_n+len(split)','pure_start = live+base_n+len(split)-1'),
      ('-pure.index(a)','-pure_active.index(a)'),
      ('assert (raw_stage(-o),8 if order<=14 else 17) in mergers',
       'assert (raw_stage(1-2*rk.XI),8) in mergers'),
    ]
    for a,b in changes:
        assert s.count(a)==1,a
        s=s.replace(a,b)
    return s

def rebuild(root):
    rk=module(checked(root,'construct.py'),root/'construct.py','rk_order12_forward_alias_base')
    rk.XI=XI
    wr=module(patched(checked(root,'weighted_regular.py')),root/'weighted_regular.py',
              'rk_order12_forward_alias_raw')
    saved=sys.modules.get('weighted_middle')
    mm=ModuleType('weighted_middle')
    mm.prepare=prepare
    sys.modules['weighted_middle']=mm
    try:
        wr.build(rk,{},12,verify_reads=True)
    finally:
        if saved is None:del sys.modules['weighted_middle']
        else:sys.modules['weighted_middle']=saved
    t=wr.CAP
    A,L,beta=t['fwd'],t['l'],t['beta']
    nf,nl,n=len(t['fo_prefix']),len(L),len(A)
    assert (nf,nl,n)==(11,31,42)
    assert {a:w for a,w in t['weight'].items()}=={1-2*a:w for a,w in W.items()}
    # Rows of the same old physical fibre receive exactly the same update.
    owner={a-1:b-1 for a,b in t['mergers']}
    k={int(j):F(q)for j,q in REC['k'].items()}
    assert set(k)=={owner.get(i,i)for i in range(nf,n) if owner.get(i,i)>=nf}
    assert all(rk.paid_integer(v.denominator)for v in k.values())
    aug,special=REC['target'],REC['merge_old']
    assert k[special]==1 and special>=nf and owner.get(special,special)==special
    assert not any(A[special][nf:])and sum(A[aug])==sum(A[special])==F(1,4)
    d=[a-b for a,b in zip(rk.pad(A[aug],nf),rk.pad(A[special][:nf],nf),strict=True)]
    assert d==list(map(F,REC['row_diff'])) and not sum(d)
    @cache
    def phi(t):
        ch=[act(s)for s in t]
        return tuple(prod(v[i]for v in ch)for i in range(nf))
    @cache
    def act(t):return tuple(rk.dot(row,phi(t))for row in A[:nf])
    low=[t for h in range(1,6)for t in wr._forests(h-1)]
    assert len(low)==17 and all(not rk.dot(d,phi(t))for t in low)
    clocks=[1-sum(row)for row in L]
    bkr=[beta[i]*k.get(owner.get(n-1-i,n-1-i),Z)for i in range(nl)]
    levels=[[(O,)*nl]]
    for h in range(5):
        cur=levels[-1]
        levels.append([tuple(rk.dot(row,v)for row in L)for v in cur]+
                      [tuple(a*b for a,b in zip(clocks,v,strict=True))for v in cur])
    assert sum(map(len,levels))==63
    assert all(not rk.dot(bkr,v)for V in levels for v in V)
    print('Checked 17 forward child zeros and all 63 weighted reverse words.')
    AC=[row.copy()for row in A]
    for i in range(nf,n):
        q=k.get(owner.get(i,i),Z)
        for j,u in enumerate(d):
            AC[i][j]+=q*u
    out,b,mergers=rk.merge(AC,[Z]*nf+beta[::-1])
    assert len(out)==24 and (special+1,aug+1) in mergers
    assert [(a,b)for a,b in mergers if b==aug+1]==[(16,9),(17,9),(25,9)]
    assert all((a,b)in mergers for a,b in t['mergers'] if b!=special+1)
    D=lcm(*(v.denominator for row in out for _,v in row),*(v.denominator for v in b))
    assert D==28868710429988352000000000000
    print('New literal aliases: (16,9), (17,9), (25,9); 24 strict physical rows.')
    return {'A':[[str(dict(row).get(j,Z))for j in range(i)]for i,row in enumerate(out)],
            'b':list(map(str,b))}

if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--source-root',type=Path,default=HERE.parent/'erk-signed-reverse')
    p.add_argument('--emit',type=Path)
    a=p.parse_args()
    text=json.dumps(rebuild(a.source_root),indent=2)+'\n'
    if a.emit:a.emit.write_text(text)
    else:assert text==(HERE/'tableau.json').read_text()

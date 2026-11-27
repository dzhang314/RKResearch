#!/usr/bin/env python3
"""Exact deterministic shared-origin port reconstruction.

Uses two checked neighboring construction sources without editing them.
Every arithmetic operation below and in the checked kernel is rational.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import comb, prod, lcm
from pathlib import Path
from types import ModuleType
import json
import sys

HERE=Path(__file__).resolve().parent
HASH={
 'construct.py':'74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7',
 'weighted_regular.py':'f0ab1a5026113602e6402ccf5bd5e6c1cd199e918ea285a74ebd16eb06d91571',
}
xi=F(2,3)
a=F(5,3)
r=F(3,2)
pad=F(5,3)
kappa=F(17280)
grid=tuple(map(F,('-2/3','-1/2','-1/3','0','1/3','1/2','2/3','5/6','1','7/6','4/3')))
vgrid=sorted(1-2*x for x in grid)

def module(src,path,name):
    obj=ModuleType(name)
    obj.__file__=str(path)
    exec(compile(src,str(path),'exec'),obj.__dict__)
    return obj

def upstream(root):
    data={}
    for name,expect in HASH.items():
        s=(root/name).read_bytes()
        assert sha256(s).hexdigest()==expect,(name,sha256(s).hexdigest())
        data[name]=s.decode()
    return data

def prepare(rk,order,vv,mul,add,scale,cardinal):
    z,o=rk.Z,rk.O
    assert order==11
    f,fo0,fr=rk.short(5)
    f=[[xi*u for u in row]for row in f]
    fo=[(lambda j,g=g:xi**j*g(j))for g in fo0]
    pin=lambda q:sum(xi**k*F(2)**k*F(-1)**(j-k)*comb(j,k)*x/(k+1)
                     for j,x in enumerate(q)for k in range(j+1))
    hf=list(zip(fo[:2],fr[:2]))
    hfrow=fr[2]
    x=2*r*r*(2*r-1)/3
    y=-r*r*(2*r-1)*(6*r-7)/6
    Q=r*r*(r-1)*(2*r-1)
    j=r*r*(1-r)/a
    raw=[[],[a],[F(1,2)-1/(8*a),1/(8*a)],
         [-1+1/(2*a),-1/(2*a),F(2)],
         [F(1,6),F(0),F(2,3),F(1,6)],
         [r-j-x-y-Q,j,x,y,Q]]
    k3=16*r*r*(1-r)**2;k4=2*r*r*(r-1)*(2*r-1)
    R=lambda p:vv(p,2*r-1)-k3*vv(p,z)-k4*vv(p,o)
    Rop=lambda k:r**k-k3*F(1,2)**k-k4
    Rrow=[z,z,-k3,-k4,z,o]
    ro=[rk.eval_at(z),rk.eval_at(o),rk.moment(0),Rop]
    rr=[rk.basis(0,6),rk.basis(4,6),[F(1,6),z,F(2,3),F(1,6),z,z],Rrow]
    fixed={F(1),F(-1,3),F(1,3)}
    donors={2*sum(row)-1 for row in raw}
    pure=tuple(sorted(donors|fixed|{pad}))
    early=sorted(set(vgrid)-set(pure))
    late=sorted(set(pure)-fixed-{F(-1)})
    assert len(pure)==8 and len(early)==3 and len(late)==4
    print('early live scalar sites in reverse centered coordinates',tuple(map(str,early)))
    print('four terminal pure correction sites',tuple(map(str,late)))
    return (f,fo,fr,5,pin,hfrow,hf,raw,ro,rr,4,[o,z,-o],[R],
        list(zip(ro[:2],rr[:2]))+[(Rop,Rrow)],vgrid,[],early,late,kappa)

def transpose_text(src):
    # Share the actual scalar mass with reverse-origin raw row 0. Omit
    # its former balancing copy and its redundant pure scalar row.
    changes=[
      ('beta = [o]*(base_n+len(split))+[weight[a] for a in early]',
       'beta = [weight[-o]]+[o]*(base_n+len(split)-1)+[weight[a] for a in early]\n'
       '    assert rk.unit(beta[0]) and beta[0]==F(243,1925)\n'
       '    print("shared reverse-origin scalar mass",beta[0])'),
      ('l += [r.copy() for r in l[:base_n+len(split)]]',
       'l += [r.copy() for r in l[1:base_n+len(split)]]'),
      ('beta += [-o]*(base_n+len(split))',
       'beta += [-o]*(base_n+len(split)-1)'),
      ('l += [probe(a) for a in pure]',
       'pure_active = [a for a in pure if a != -o]\n    l += [probe(a) for a in pure_active]'),
      ('beta += [weight[a] for a in pure]',
       'beta += [weight[a] for a in pure_active]'),
      ('forward_factor = [o,-o] if order in (15,16) else h',
       'forward_factor = [F(1,3),F(2,3),F(-1)]'),
      ('primal = beta[rev_h]*coeff',
       'primal = beta[rev_h]*coeff/(beta[rev_j] if rev_j<base_n+len(split) else o)'),
      ('assert len(out)=={11:23,12:26,13:30,14:33,15:40,16:45,17:53,18:60,19:66,20:72}[order]',
       'assert len(out)==22, len(out)'),
      ('pure_start = live+base_n+len(split)','pure_start = live+base_n+len(split)-1'),
      ('-pure.index(a)','-pure_active.index(a)'),
      ('assert (raw_stage(-o),8 if order<=14 else 17) in mergers',
       'assert (raw_stage(F(-1,3)),8) in mergers'),
      ('assert (raw_stage(z),9) in mergers',
       'assert (raw_stage(F(1,3)),9) in mergers\n'
       '        print("full forward row merges",tuple((raw_stage(x),j) '
       'for x,j in ((o,1),(F(-1,3),8),(F(1,3),9))))'),
    ]
    for expect,new in changes:
        assert src.count(expect)==1,expect
        src=src.replace(expect,new)
    return src

def exact_data(root):
    old=upstream(root)
    rk=module(old['construct.py'],root/'construct.py','rk_order11_shared_base')
    wr=module(transpose_text(old['weighted_regular.py']),root/'weighted_regular.py','rk_order11_shared_raw')
    oldmiddle=sys.modules.get('weighted_middle')
    mm=ModuleType('weighted_middle')
    mm.prepare=prepare
    sys.modules['weighted_middle']=mm
    try:
        data=json.loads(wr.build(rk,{},11,verify_reads=True))
    finally:
        if oldmiddle is None:del sys.modules['weighted_middle']
        else:sys.modules['weighted_middle']=oldmiddle
    A=[list(map(F,r))for r in data['A']];w=list(map(F,data['b']))
    den=lcm(*(x.denominator for x in (*w,*(a for r in A for a in r))))
    assert den==941072888448000
    sf=[(a, sum(wi for row,wi in zip(A,w)if sum(row)==a))for a in grid]
    for j in range(11):
        assert sum(a**j*b for a,b in sf)==F(1,j+1)
    assert [w[i]for i,row in enumerate(A)if sum(row)==1]==[F(243,1925)]
    @lru_cache(None)
    def phi(t):
        vals=[act(u)for u in t]
        return tuple(prod(row[i]for row in vals)for i in range(22))
    @lru_cache(None)
    def act(t):
        v=phi(t)
        return tuple(sum(x*y for x,y in zip(r,v))for r in A)
    @lru_cache(None)
    def order(t):return 1+sum(map(order,t))
    @lru_cache(None)
    def factorial(t):return order(t)*prod(map(factorial,t))
    def gap(t):
        return factorial(t)*sum(a*b for a,b in zip(w,phi(t)))-1
    t1=((),)*11;t2=((),)*5+(((),)*5,)
    g=[(k,gap(k))for k in (t1,t2)]
    assert [h for _,h in g]==[F(8561,3849120),F(-1309396673493832996421,13471920)]
    t=((),)*4;v=(((t,),),);h=((),(),(),v)
    assert order(h)==12 and factorial(h)==20160 and gap(h)==F(-16,2673)
    data.update(D=str(den),defects=[[t,str(z)]for t,z in g],scalar_nodes=list(map(str,grid)),
                scalar_weights=[str(wj)for _,wj in sf],reverse_a=str(a),reverse_r=str(r),
                padding=[str(pad)],injection=str(kappa))
    return data

if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--source-root',type=Path,default=HERE.parent/'erk-signed-reverse')
    p.add_argument('--emit',type=Path)
    args=p.parse_args()
    obj=exact_data(args.source_root)
    txt=json.dumps(obj,indent=2)+'\n'
    if args.emit:args.emit.write_text(txt)
    else:assert txt==(HERE/'tableau.json').read_text()

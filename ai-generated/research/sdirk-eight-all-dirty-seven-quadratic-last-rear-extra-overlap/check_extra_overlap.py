"""Exact guarded replay: one-extra rear D, overlap at its nonterminal label."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent /
                      'sdirk-eight-all-dirty-seven-quadratic-last-rear-terminal-overlap'))
from projection import project,poly,lp,DD,NN,K,pairs
from check_terminal_overlap import K_h,spec_H
from flint import nmod_poly as NP
from sympy.polys.rings import ring
from sympy import isprime

TABLE={
 ('A2','A2'):{(2,1):('raw',11,5,17,20,16),(36,1):('slope',31,27,18,17),
             (3,2):('taps',11,10,18,16),(12,2):('taps',29,0,18,16),
             (18,2):('taps',31,1,18,16),(27,2):('taps',11,8,18,16)},
 ('A2','A3'):{(4,1):('pair',19,13,18,17),(36,1):('slope',31,27,18,17),
             (3,2):('taps',11,10,18,16),(12,2):('taps',29,0,18,16),
             (18,2):('taps',31,1,18,16),(27,2):('taps',11,8,18,16)},
 ('A2','S'):{(36,1):('slope',31,27,18,17),(3,2):('taps',11,10,18,16),
            (12,2):('taps',29,0,18,16),(18,2):('taps',31,1,18,16),
            (27,2):('taps',11,8,18,16)},
 ('A3','A2'):{(18,1):('slope',23,15,9,8),(4,1):('pair',19,14,9,8),
             (18,2):('taps',31,1,9,7)},
 ('A3','A3'):{(18,1):('slope',23,15,9,8),(2,1):('raw',11,5,8,14,13),
             (18,2):('taps',31,1,9,7)},
 ('A3','S'):{(18,1):('slope',23,15,9,8),(18,2):('taps',31,1,9,7)},
 ('S','A2'):{(6,3):('slope',19,16,9,6),(9,4):('taps',13,2,9,5)},
 ('S','A3'):{(6,3):('slope',19,16,9,6),(9,4):('taps',13,10,9,5)},
 ('S','S'):{(2,1):('raw',11,5,7,8,7),(6,3):('slope',19,16,9,6),
            (9,4):('taps',13,2,9,5)}}
def sp(f,p,h,keep=1):
    ds=f.degrees()
    out=[0]*(ds[keep]+1)
    n=1-keep
    powers=[pow(h,i,p) for i in range(ds[n]+1)]
    for ix,a in f.to_dict().items():out[ix[keep]]+=int(a)*powers[ix[n]]
    return NP(out,p)
def reduce(f,p,h):
    vals=[]
    for j in range(f.degree()+1):
        a=f.get((j,),f.ring.domain.zero)
        v=0
        aa=a.to_list() if hasattr(a,'to_list') else [a]
        for q in aa:
            assert int(q.denominator)%p!=0
            v=(v*h+int(q.numerator)*pow(int(q.denominator),-1,p))%p
        vals.append(v)
    return NP(vals,p)
def gcd(a,b):
    while b:
        c=a%b
        a,b=b,(c.monic() if c else c)
    return a.monic() if a else a
def trim(a,guards):
    for g in guards:
        if g:g=g.monic()
        while (z:=gcd(a,g)).degree()>0:a=a.exquo(z).monic()
    return a
def exact_guards(front,rear,gs,kind):
    # Masks in the shared projection are ordered by the pair tables, then the
    # base physical clocks/m, followed by the three centered Legendre guards
    # and the recovered affine/graph data. Name the groups before using them.
    nfront=4 if front=='S' else 5
    nrear=4 if rear=='S' else 5
    base_clock_and_scale=3
    off=nfront+nrear+base_clock_and_scale
    clocks=gs[off:off+10] # combinations([0,s,t,H,d],2)
    legendre_and_parity=gs[off+10:off+13]
    anchor_slope,M0,Ms,Mt,l0,l1=gs[off+13:off+19]
    assert len(legendre_and_parity)==3 and len(clocks)==10
    if kind=='taps':return gs[:nfront]
    if kind=='pair':return [clocks[4],M0] # s - t, M_3(0)
    assert kind=='slope'
    return [anchor_slope,l1]
def run():
    covered=set();total=0
    for w,f,r,ff,rows,gs,_ in project(('extra',)):
        assert w=='extra'
        covered.add((f,r))
        tab=TABLE[f,r]
        assert {(q.total_degree(),n) for q,n in ff}==set(tab) and len(ff)==len(tab)
        for hf,n in ff:
            tag=hf.total_degree(),n
            mode,p,h,*ds=tab[tag]
            assert isprime(p)
            hmod=sp(hf,p,0,0)
            assert hmod.degree()==tag[0] and not hmod(h) and hmod.derivative()(h)
            field,H=K_h(hf)
            D,_=ring('d',field)
            if mode=='raw':
                ds0=[spec_H(a,D,H).degree() for a in rows]
                assert ds0==ds
                red=[sp(a,p,h) for a in rows]
                assert any(a.degree()==delta and delta>0 for a,delta in zip(red,ds))
            else:
                E=spec_H(rows[0],D,H).monic()
                assert E.degree()==ds[0]
                G=[spec_H(g,D,H) for g in exact_guards(f,r,gs,mode)]
                assert all(G)
                if mode=='slope':
                    G=[gcd(*G)]
                    assert G[0].degree()==ds[0]-ds[1]
                e=trim(E,G)
                assert e.degree()==ds[1]>0
                em=reduce(e,p,h)
                assert em.degree()==e.degree() and em.leading_coefficient()==1
                red=[em,*[sp(a,p,h) for a in rows[1:]]]
            assert red[0].gcd(red[1]).gcd(red[2]).degree()==0
            total+=1
            print(f,r,tag,mode,p,h,'verified',flush=True)
    assert covered==set(TABLE) and total==32
    print('all nine extra-D overlap phase charts excluded',flush=True)
if __name__=='__main__':run()

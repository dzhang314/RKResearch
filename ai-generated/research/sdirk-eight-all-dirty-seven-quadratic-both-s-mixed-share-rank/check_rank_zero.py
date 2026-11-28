"""Exact rank-zero exclusion in all nine both-S mixed one-share charts."""
from mixed_share_common import CASES,rank_project
from field_fibres import field,spec,gcd,trim
from sympy.polys.rings import ring

H0=('clocks',1);t0=('clocks',4);C0=('clocks',10);N0=('rear_taps',4)
expect={
 'A1A2':{(2,0):H0,(7,0):t0},'A1A3':{(5,0):H0,(9,0):C0,(12,0):N0},
 'A1S':{(2,0):H0},'A2A2':{(5,0):H0,(9,0):C0},
 'A2A3':{(12,0):N0,(8,0):H0},'A2S':{(5,0):H0},'SA2':{(2,0):H0},
 'SA3':{(5,0):H0,(12,0):N0},'SS':{(2,18):C0,(2,8):H0}}
def run(cases):
    n=0
    for mode in cases:
        factors,rows,G=rank_project(mode)
        masks=expect[mode];seen=set()
        for q,k in factors:
            q0,K,u=field(q)
            deg=q0.degree()
            tag=deg,int(q0.LC()) if mode=='SS' else 0
            assert tag not in seen and k==1
            seen.add(tag)
            R,_=ring('v',K)
            f=lambda e:spec(e,R,u)
            E,*other=map(f,rows)
            assert E
            E=E.monic()
            d=E
            for r in other:d=gcd(d,r%E)
            assert d.degree()==1
            name,i=masks[tag]
            assert trim(d,f(G[name][i]))==R.one
            print(mode,tag,'exact linear row excluded by',name,i,flush=True)
            n+=1
        assert seen==set(masks)
    assert n==sum(len(expect[mode]) for mode in cases)
    print('mixed one-shared rank-zero charts/fibres excluded',len(cases),n,flush=True)
if __name__=='__main__':
    from sys import argv
    run(argv[1:] or CASES)

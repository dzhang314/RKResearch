"""Deterministic theorems for the two final disjoint one-extra-D rear charts."""
import argparse,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent.parent
for name in ('last-rear-disjoint-more','last-rear-disjoint-two-star'):
    sys.path.insert(0,str(BASE/('sdirk-eight-all-dirty-seven-quadratic-'+name)))
from fast_fraction import frame,strip
from check_more_disjoint import (
    check_case,cert,raw,a2_slope,a2_q0,a2_q1,a2_q2,a2_3,a2_12,a2_18,a2_27)
from guarded_crt import resultant,fast_kernel

ROW_DEGREES={'A2':[(18,18),(101,90),(112,98)],
             'A3':[(18,18),(101,90),(52,50)]}
PROJECTIONS={'A2':((2937,3253),(2077,2305)),
             'A3':((2937,1599),(2083,1185))}
TABLE={
 'A2':{
    (24,1,0):cert(29,22,18,17,('base',7)),
    (36,2,0):a2_slope,(4,8,24):a2_q0,(4,9,-60):a2_q1,
    (4,9,-102):a2_q2,(2,9,0):raw(17,82,89),
    (3,20,0):a2_3,(27,20,0):a2_27,(18,20,0):a2_18,
    (12,21,0):cert(41,6,18,16,('front_taps',1))},
 'A3':{
    (36,2,0):a2_slope,(2,3,0):raw(17,82,47),
    (4,3,24):a2_q0,(4,3,-60):a2_q1,(4,3,-102):a2_q2,
    (3,10,0):a2_3,(12,10,0):a2_12,(18,10,0):a2_18,(27,10,0):a2_27}}
def run(modes,accelerator=None):
    count=0
    for rear in modes:
        f='A2'
        rows,guards=frame(f,rear)
        assert [tuple(map(int,z.degrees())) for z in rows]==ROW_DEGREES[rear]
        E,X,Y=rows
        print(f,rear,'rows',ROW_DEGREES[rear],flush=True)
        hs=[a for a in sum(guards.values(),[]) if not a.degrees()[1]]
        a,b=[resultant(E,z,accelerator) for z in (X,Y)]
        raw_deg=a.total_degree(),b.total_degree()
        u,v=strip(a,hs),strip(b,hs)
        guard_deg=u.total_degree(),v.total_degree()
        assert (raw_deg,guard_deg)==PROJECTIONS[rear]
        G=u.gcd(v)
        assert G
        print(f,rear,'projected degrees',raw_deg,guard_deg,flush=True)
        T=TABLE[rear]
        check_case(f,rear,G.factor()[1],rows,guards,T)
        count+=len(T)
    print('complete final disjoint phase exclusions',modes,'with',count,'verified fibres',flush=True)
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--rear',choices=('A2','A3'))
    parser.add_argument('--fast-library')
    a=parser.parse_args()
    run((a.rear,) if a.rear else ('A2','A3'),fast_kernel(a.fast_library) if a.fast_library else None)

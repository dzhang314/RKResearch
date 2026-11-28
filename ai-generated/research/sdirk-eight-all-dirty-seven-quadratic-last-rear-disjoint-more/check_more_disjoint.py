"""Exact algebraic fibres for the remaining disjoint-prefix phase charts."""
from pathlib import Path
import sys
HERE=Path(__file__).resolve()
RESEARCH=HERE.parent.parent
for name in ('terminal-overlap','extra-overlap','disjoint-two-star'):
    sys.path.insert(0,str(RESEARCH/('sdirk-eight-all-dirty-seven-quadratic-last-rear-'+name)))
from check_extra_overlap import sp,reduce,gcd,trim
from check_terminal_overlap import spec_H,K_h
from disjoint_projection import project
from sympy.polys.rings import ring
from sympy import isprime
from primitive_resultant import resultant

def tag(f,n):
    d=f.total_degree()
    # H^2 coefficient distinguishes simultaneously present same-degree quartics.
    return d,n,int(f.to_dict().get((2,0),0)) if d==4 else 0
def cert(p,h,n,m,*g):
    return (p,h),n,m,g
def raw(x,y,z):return (11,5),(x,y,z),None,()
slope=cert(23,15,9,8,('gcd-slopes',-1))
tap18=cert(31,1,9,7,('front_taps',2))
q0=cert(11,7,9,8,('base',3))
q1=cert(19,14,9,8,('slopes',1))
q2=cert(13,10,9,8,('base',4))
star_slope=cert(19,16,9,6,('gcd-slopes',-1))
star_small=cert(17,2,9,6,('base',2),('slopes',1))
star_4=cert(29,23,9,6,('base',2),('base',4),('slopes',1))
star_9=cert(13,10,9,5,('front_taps',3))
a2_slope=cert(31,27,18,17,('gcd-slopes',-1))
a2_3=cert(11,10,18,16,('front_taps',1))
a2_12=cert(29,0,18,16,('front_taps',1))
a2_18=cert(31,1,18,16,('front_taps',2))
a2_27=cert(11,8,18,16,('front_taps',2))
a2_q0=cert(11,7,18,17,('base',4))
a2_q1=cert(19,14,18,17,('slopes',1))
a2_q2=cert(13,5,18,17,('slopes',1))
TABLE={
 ('A2','S'):{
  (4,2,24):a2_q0,(4,2,-60):a2_q1,(4,2,-102):a2_q2,
  (36,2,0):a2_slope,(2,3,0):raw(17,39,47),
  (3,8,0):a2_3,(12,8,0):a2_12,(18,8,0):a2_18,(27,8,0):a2_27},
 ('A3','A2'):{
  (18,2,0):slope,(4,8,24):q0,(4,8,-102):q2,
  (2,9,0):raw(8,49,53),(4,9,-60):q1,(18,20,0):tap18},
 ('A3','A3'):{
  (12,1,0):cert(19,12,9,8,('base',7)),
  (18,2,0):slope,(4,3,-60):q1,(4,3,-102):q2,
  (2,3,0):raw(8,49,29),(4,4,24):q0,(18,10,0):tap18},
 ('S','A2'):{
  (6,6,0):star_slope,(4,16,754):star_4,(1,18,0):star_small,
  (2,18,0):raw(7,35,38),(9,40,0):star_9},
 ('S','A3'):{
  (1,6,0):star_small,(4,6,754):star_4,(6,6,0):star_slope,
  (2,6,0):raw(7,35,20),(9,20,0):star_9},
}

def check_case(f,r,ff,rows,gs,T):
    assert {tag(q,n) for q,n in ff}==set(T) and len(ff)==len(T)
    for P,n in ff:
        t=tag(P,n);(p,h),d0,d1,guards=T[t]
        assert isprime(p)
        Hmod=sp(P,p,0,0)
        assert Hmod.degree()==t[0] and not Hmod(h) and Hmod.derivative()(h)
        K,H=K_h(P);D,_=ring('d',K)
        spec=lambda a:spec_H(a,D,H)
        if d1 is None:
            assert tuple(spec(a).degree() for a in rows)==d0
            red=[sp(a,p,h) for a in rows]
            assert any(a.degree()==j and j>0 for a,j in zip(red,d0))
        else:
            E=spec(rows[0]).monic()
            assert E.degree()==d0
            for k,i in guards:
                if k=='gcd-slopes':
                    a,b=map(spec,gs['slopes'])
                    assert a and b
                    g=gcd(a,b)
                else:g=spec(gs[k][i])
                assert g
                E=trim(E,[g])
            assert E.degree()==d1>0
            ep=reduce(E,p,h)
            assert ep.degree()==d1 and ep.leading_coefficient()==1
            red=[ep,*[sp(a,p,h) for a in rows[1:]]]
        assert red[0].gcd(red[1]).gcd(red[2]).degree()==0
        print(f,r,t,p,h,'d profile',d0,d1,'verified',flush=True)
PROJECTIONS={
 ('A2','S'):(955,1185),('A3','A2'):(928,1018),('A3','A3'):(925,555),
 ('S','A2'):(829,919),('S','A3'):(829,459)}
def run(phases=(),fast_library=None,primitive_a2=False):
    # The shared scaling engine is imported only by the command-line runner;
    # the later packet may safely import this file's fixed-fibre helpers.
    final=RESEARCH/'sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-final'
    sys.path.insert(0,str(final))
    from fast_fraction import frame,strip
    from guarded_crt import resultant as crt_resultant,fast_kernel
    acc=fast_kernel(fast_library) if fast_library else None
    assert set(phases) <= {f+'-'+r for f,r in TABLE}
    verified=0
    for (f,r),T in TABLE.items():
        if phases and f+'-'+r not in phases:continue
        rows,guards=frame(f,r)
        E,X,Y=rows
        if f=='A2':
            method=resultant if primitive_a2 else lambda a,b:crt_resultant(a,b,acc)
        else:method=lambda a,b:a.resultant(b,'d')
        Hguards=[a for a in sum(guards.values(),[]) if not a.degrees()[1]]
        print(f,r,'rows',[a.degrees() for a in rows],flush=True)
        U,V=[strip(method(E,z),Hguards) for z in (X,Y)]
        assert (U.total_degree(),V.total_degree())==PROJECTIONS[f,r]
        assert U and V
        G=U.gcd(V)
        assert G
        check_case(f,r,G.factor()[1],rows,guards,T)
        verified+=len(T)
    if not phases:assert verified==32
    print('verified',verified,'exact H fibres',flush=True)
if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('phases',nargs='*')
    ap.add_argument('--fast-library')
    ap.add_argument('--primitive-a2',action='store_true')
    a=ap.parse_args()
    run(a.phases,a.fast_library,a.primitive_a2)

"""Fixed exact fibres for two disjoint-prefix true rear-star charts."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
for name in ('terminal','extra'):
    sys.path.insert(0,str(ROOT/('sdirk-eight-all-dirty-seven-quadratic-last-rear-'+name+'-overlap')))
from check_extra_overlap import sp,reduce,gcd,trim
from check_terminal_overlap import spec_H,K_h
from disjoint_projection import project
from sympy.polys.rings import ring
from sympy import isprime

# Qualify the three distinct quartics (4,2) by their H^2 coefficient.
def tag(f,n):
    deg=f.total_degree()
    return deg,n,int(f.to_dict()[(2,0)]) if (deg,n)==(4,2) else 0
TABLE={
 ('A3','S'):{
  (18,2,0):((23,15),9,8,[('gcd-slopes',-1)]),
  (4,2,24):((11,7),9,8,[('base',3)]),
  (4,2,-60):((19,14),9,8,[('slopes',1)]),
  (4,2,-102):((13,10),9,8,[('base',4)]),
  (2,3,0):((11,5),(8,24,29),None,[]),
  (18,8,0):((31,1),9,7,[('front_taps',2)])},
 ('S','S'):{
  (12,1,0):((17,11),9,6,[('base',7)]),
  (4,5,0):((29,23),9,6,[('base',2),('base',4),('slopes',1)]),
  (1,6,0):((17,2),9,6,[('base',2),('slopes',1)]),
  (6,6,0):((19,16),9,6,[('gcd-slopes',-1)]),
  (2,6,0):((11,5),(7,15,20),None,[]),
  (9,16,0):((13,10),9,5,[('front_taps',3)])}}
def check_case(f,r,ff,rows,gs,T):
    assert {tag(q,n) for q,n in ff}==set(T) and len(ff)==len(T)
    for P,n in ff:
        t=tag(P,n);(p,h),d0,d1,guards=T[t]
        assert isprime(p)
        Hmod=sp(P,p,0,0)
        assert Hmod.degree()==t[0] and not Hmod(h) and Hmod.derivative()(h)
        K,H=K_h(P);D,d=ring('d',K)
        spec=lambda a:spec_H(a,D,H)
        # Base order in the generated frame:
        # [m,H,d,d-H,2d-H,u-2,L4(H),L4(d),s,s-d,s-H].
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
def run():
    for (f,r),T in TABLE.items():
        ff,rows,gs=project(f,r)
        check_case(f,r,ff,rows,gs,T)
    print('all twelve fibres of disjoint A3/star and star/star excluded',flush=True)
if __name__=='__main__':run()

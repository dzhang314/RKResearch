"""Projective mixed shared-D arithmetic cases: four phase profiles and fixed places."""
from pathlib import Path
import sys
BASE=Path(__file__).resolve().parent.parent
stars=BASE/'sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-stars'
sys.path.insert(0,str(stars))
from projective_share import regular_projection
from field_fibres import field,spec,trim
from check_star_cases import sp,reduce
from sympy.polys.rings import ring
from sympy import isprime
from argparse import ArgumentParser
PROFILES={
 'A1A2':[655,1071,587,980],
 'A2A2':[563,933,573,948],
 'A1A3':[637,1051,473,805],
 'A2A3':[594,982,532,889]}
# (factor degree, multiplicity) -> true guard, pre/post exact degrees, p/u place
FIBRES={
 'A1A2':{(7,2):('clocks',4,17,15,19,11)},
 'A2A2':{(9,2):('clocks',10,16,15,11,6)},
 'A1A3':{(9,2):('clocks',10,16,15,31,21),
          (12,4):('rear_taps',4,16,14,37,14)},
 'A2A3':{(12,4):('rear_taps',4,17,15,17,6)}}
def check_case(mode,factors,rows,G,degrees):
    tab=FIBRES[mode]
    assert degrees==PROFILES[mode]
    assert len(factors)==len(tab)
    assert {(q.total_degree(),n) for q,n in factors}==set(tab)
    for q,n in factors:
        dg=q.total_degree()
        mask,idx,before,after,p,h=tab[dg,n]
        _,K,u=field(q)
        R,v=ring('v',K)
        f=lambda a:spec(a,R,u)
        E=f(rows[0]).monic()
        assert E.degree()==before and f(G[mask][idx])
        Z=trim(E,f(G[mask][idx]))
        assert Z.degree()==after>0
        assert isprime(p)
        U=sp(q,p,0,0)
        assert U.degree()==dg and not U(h) and U.derivative()(h)
        D=reduce(Z,p,h)
        assert D.degree()==after and D.leading_coefficient()==1
        for t in rows[1:]:D=D.gcd(sp(t,p,h))
        assert D.degree()==0
        print(mode,'degree',dg,'exact trim',before,'->',after,
              'and unit residue gcd',p,h,flush=True)
def run(modes,accelerator=None):
    method=None
    if accelerator:
        crt=BASE/'sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-final'
        sys.path.insert(0,str(crt))
        from guarded_crt import resultant,fast_kernel
        acc=fast_kernel(accelerator)
        method=lambda a,b:resultant(a,b,acc)
    total=0
    for mode in modes:
        facts,rows,G,degrees=regular_projection(mode,method)
        check_case(mode,facts,rows,G,degrees)
        total+=len(facts)
    print('mixed one-share arithmetic charts excluded',len(modes),'with',total,
          'fixed complete-field certificates',flush=True)
if __name__=='__main__':
    p=ArgumentParser()
    p.add_argument('modes',nargs='*')
    p.add_argument('--fast-library')
    a=p.parse_args()
    run(a.modes or list(PROFILES),a.fast_library)

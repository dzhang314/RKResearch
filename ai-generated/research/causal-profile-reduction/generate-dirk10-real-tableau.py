#!/usr/bin/env python3
"""Regenerate the literal exact quotient coefficient export and decimal view.

Run without arguments to compare bytes without editing the repository, or
pass --out DIRECTORY to write the two regenerated outputs there. The
separate mathematical replay checks every rooted condition.
"""
import argparse
from decimal import Decimal, localcontext
import json
from pathlib import Path
import runpy
import tempfile


def build(source, dest):
    m = runpy.run_path(str(source/'check-dirk10-real-algebraic.py'))
    E, Q, It = m['E'], m['Q'], m['It']
    ev, eval_interval = m['ev'], m['it_eval']
    K,T,V = m['K'],m['T'],m['V']
    c,b,g,h,G=m['polynomials_on_layout']()
    A=m['solve_tableau'](c,b,g,h,G)

    # The precise table is independent of the floating-point display.
    def coords(x):
        if isinstance(x,E):
            n=len(x.alg.mod)-1
            z=x.alg.down(0)
            return [coords(x.c[i]if i<len(x.c)else z) for i in range(n)]
        x=Q(x)
        return [str(x.numerator),str(x.denominator)]

    z11=11*sum(w*x**10 for w,x in zip(b,c))-1
    payload={
        'format':'nested polynomial coordinate lists, degrees ascending; leaves are decimal strings [numerator,positive denominator]',
        'basis_levels':'outer r9 (degree 0,1), middle r8 (degree 0,1,2), inner k (degree 0,1,2), then rational coefficient',
        'polydata':'monic modulus coefficient lists (low-first) in each underlying algebra, including leading one',
        'mod_k':[coords(x) for x in K.mod],
        'mod_r8':[coords(x) for x in T.mod],
        'mod_r9':[coords(x) for x in V.mod],
        'real_roots_open_decimal_brackets':{
            'k':['-2.04748','-2.04747'], 'r8':['0.6377','0.6380'], 'r9':['0.8664','0.8668']},
        'matrix_lower_triangular':[[coords(x)for x in row]for row in A],
        'weights':[coords(x)for x in b],
        'nodes':[coords(x)for x in c],
        'star11_residual':[coords(z11),coords(1/z11)],
    }
    dest.mkdir(parents=True,exist_ok=True)
    exact=dest/'dirk-order10-eleven-real-coefficients.json'
    exact.write_text(json.dumps(payload,sort_keys=True,indent=None,separators=(',',':'))+'\n')

    def refine(box, coeff):
        lo,hi=box.a,box.b
        sl=ev(coeff,lo).sign()
        assert sl*ev(coeff,hi).sign()==-1
        for _ in range(99):
            mid=(lo+hi)/2
            value=ev(coeff,mid).sign()
            if not value:
                break
            if value==sl:
                lo=mid
            else:
                hi=mid
        return It(lo,hi)
    ri=eval_interval.__globals__
    coeff=[eval_interval(q)for q in m['SUF']]
    ri['ilo']=refine(ri['ilo'],coeff)
    ri['imi']=refine(ri['imi'],coeff)

    def decimal(x):
        box=eval_interval(x)
        if not isinstance(box,It):
            box=It(Q(box),Q(box))
        assert box.b-box.a<Q(1,10**18)
        mid=(box.a+box.b)/2
        with localcontext() as ctx:
            ctx.prec=45
            return format(Decimal(mid.numerator)/Decimal(mid.denominator),'.15g')

    approx=dest/'dirk-order10-eleven-real-decimal.csv'
    with approx.open('w')as out:
        out.write('physical_stage,c,b,'+','.join('A_'+str(j+1)for j in range(11))+'\n')
        for i,(p,w,row) in enumerate(zip(c,b,A),1):
            line=[str(i),decimal(p),decimal(w),*[decimal(q)for q in row],*('0'for _ in range(11-len(row)))]
            out.write(','.join(line)+'\n')
    return exact,approx


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    source=Path(__file__).resolve().parent
    if args.out:
        build(source,args.out)
        return
    with tempfile.TemporaryDirectory()as td:
        for recreated in build(source,Path(td)):
            assert recreated.read_bytes()==(source/recreated.name).read_bytes(), recreated.name
    print('Both exact and decimal exports reproduce byte for byte.')


if __name__=='__main__':
    main()

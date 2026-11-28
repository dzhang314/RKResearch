"""Full univariate projections and fixed places; no bivariate gcd ingress."""
import argparse
from sympy import isprime
from projection_residual import *
from places import spec,special_fb,stable_common
from field_fmpq import Field
from flint import nmod_poly

sys.path.insert(0,str(RESEARCH/'sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-final'))
from guarded_crt import resultant,fast_kernel

S_SITES=[
 (2,1,1511,823,0), (4,1,1523,812,0), (4,1,1523,764,0),
 (4,1,1523,1181,0), (4,1,1523,924,0), (8,1,1523,680,0),
 (122,1,1523,309,0), (140,1,1523,131,0), (168,1,1523,837,0),
 (1449,1,1493,1294,0), (4,2,1523,47,0), (8,2,1523,1187,0),
 (4,4,1523,885,0), (1,6,1523,2,0), (4,9,1523,1215,0),
 (8,9,1031,655,2), (12,16,997,471,4), (4,27,1109,466,6)
]
A3_SITES=[
 (2,1,1009,247,0),(3,1,1013,911,0),(5,1,997,60,0),
 (8,1,1009,305,0),(24,1,997,517,0),(48,1,997,119,0),
 (48,1,997,783,0),(104,1,997,104,0),(272,1,1009,26,0),
 (54,2,1031,896,0),(97,2,997,237,0),(802,2,997,177,0),
 (2,3,1009,571,0),(12,4,997,497,0),(24,4,997,298,0),
 (8,20,1031,655,4),(12,20,997,471,4)
]
CZ2=fmpz_mpoly_ctx.get(('H','d'),'lex')
def eliminate(P,Q,accelerator):
    def to2(x):
        assert not x.degrees()[2]
        return CZ2.from_dict({(i,j):k for (i,j,h),k in x.to_dict().items()})
    R=resultant(to2(P),to2(Q),accelerator)
    return CZ.from_dict({(i,j,0):int(v) for (i,j),v in R.to_dict().items()})
def at_place(f,n,ps,bs,table):
    n0=f.total_degree()
    for d,e,p,h,delta in table:
        if (n0,n)!=(d,e):continue
        assert p>3 and isprime(p)
        res=spec(f,p,1,var=0)
        if res.degree()!=d or res(h) or not res.derivative()(h):continue
        G=stable_common([spec(x,p,h) for x in ps],[x.degrees()[1] for x in ps])
        if G is None or G.degree()!=delta:continue
        assert delta>=0
        if delta:
            roots=G.roots()
            if sum(k for v,k in roots)!=delta:continue
            lucky=True
            for v,k in roots:
                B=stable_common([special_fb(x,p,h,int(v)) for x in bs],[x.degrees()[2] for x in bs])
                if B is None or B.degree()!=0:
                    lucky=False
                    break
            if not lucky:continue
        print('fixed place, H-factor deg/exp',d,e,'p,h',p,h,'a-gcd degree',delta,flush=True)
        return
    raise AssertionError(f'No complete stable place for degree/multiplicity {(n0,n)}')
def a3_quartic(f,n,ps):
    assert n==82 and f==ip((H**4-12*H**3-6*H**2+12*H+6).n)
    p,h=1109,466
    assert isprime(p)
    res=spec(f,p,1,var=0)
    assert res.degree()==4 and not res(h) and res.derivative()(h)
    K=Field(f)
    true_mask=K.trans(ip(D(a/2).n))
    assert len(true_mask)==4
    def local(co):
        # Exact coefficient in Q[H]/f, then reduce at a specified place.
        return int(nmod_poly([int(x.numerator)%p*
                    pow(int(x.denominator)%p,-1,p)%p for x in co.coeffs()],p)(h))
    rr=[]
    expect=[(46,34),(78,54),(78,54),(54,39),(54,39),(77,53)]
    for X,deg in zip(ps,expect,strict=True):
        a0=K.trans(X)
        a1=K.discard(a0,true_mask)
        assert a0 and a1 and (len(a0)-1,len(a1)-1)==deg
        z=nmod_poly([local(x) for x in a1],p)
        assert z.degree()==len(a1)-1
        rr.append(z)
    g=rr[0]
    for z in rr[1:]:g=g.gcd(z)
    assert g.is_one()
    print('A2/A3 field quartic: exact D-factor stripping and stable unit a-gcd',flush=True)

def certify(mode,accelerator):
    A,B,pure=residual_rows(mode)
    i,j=(1,2) if mode=='S' else (0,4)
    P=eliminate(A[i],A[j],accelerator)
    want=2378 if mode=='S' else 3486
    assert P.degrees()==(want,0,0)
    fs=strip(P,pure).factor()[1]
    table=S_SITES if mode=='S' else A3_SITES
    expected=[(d,e) for d,e,_,_,_ in table]+([] if mode=='S' else [(4,82)])
    assert [(f.total_degree(),e) for f,e in fs]==expected
    for f,e in fs:
        if mode=='A3' and (f.total_degree(),e)==(4,82):
            a3_quartic(f,e,A)
        else:
            at_place(f,e,A,B,table)
    print(mode,'full regular degree-two residual chart verified',flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--fast-library')
    parser.add_argument('--mode',choices=CASES)
    args=parser.parse_args()
    acc=fast_kernel(args.fast_library) if args.fast_library else None
    for phase in ([args.mode] if args.mode else CASES):
        certify(phase,acc)

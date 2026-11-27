import arith_model as A
import json
from flint import fmpq_poly,fmpq,fq_default_ctx,fq_default_poly_ctx,nmod_poly,fmpz_mod_poly_ctx
from collections import Counter
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/"sdirk-eight-repeated-first"))
from rational_field import E,poly_eval,poly_gcd,divmod_coeff

K=A.K;m=A.m;u=A.u
def residue_bound(f,g,mod):
    dm=mod.degree()
    best=min(len(f)-1,len(g)-1)
    for p in (43,47,53,59,61,67,71,73,79,83,89,97,101,103):
        nv=lambda c:int(c.numerator)*pow(int(c.denominator),-1,p)%p
        mm=nmod_poly([nv(c) for c in mod.coeffs()],p)
        if mm.degree()!=dm:continue
        for md,e in mm.factor()[1]:
            if md.degree()==1:
                R=fq_default_ctx(p);t=R(-int(md[0])*pow(int(md[1]),-1,p)%p)
            else:
                R=fq_default_ctx(modulus=fmpz_mod_poly_ctx(p)(list(map(int,md.coeffs()))));t=R.gen()
            P=fq_default_poly_ctx(R)
            def cp(C):
                a=R.zero()
                for c in C.a.coeffs()[::-1]:a=t*a+R(nv(c))
                return a
            try: F,G=P(list(map(cp,f))),P(list(map(cp,g)))
            except ValueError: continue
            if F.degree()!=len(f)-1 or G.degree()!=len(g)-1:continue
            bound=F.gcd(G).degree()
            best=min(best,bound)
            break
        if best==1:return best
    return best

def recover(Fn,Gn,mod):
    E.P=mod;M=E([0,1]);mP=[M**j for j in range(64)]
    def build(V):
        if not V:return []
        pp=[E(0) for j in range(V.degree(u.numer)+1)]
        for (i,j),qv in V.items():pp[j]=pp[j]+mP[i]*E(qv)
        while pp and not pp[-1]:pp.pop()
        return pp
    if M==1:return 'third pair at exhausted first clock',0,0,dict()
    F,G=build(Fn),build(Gn)
    assert F and G
    bound=residue_bound(F,G,mod)
    cnt=Counter()
    k0=A.k
    checks=[]
    ts=[3-m,5-m,m-1,m-1-u,m-1-2*u]
    gs=[A.h,A.h,A.H,A.H*k0,A.H*A.q]
    for i in range(5):
        checks.append(('third pair at exhausted first clock',build((ts[i]-(1-m)).numer)))
        for j in range(i):
            a=build((ts[i]-ts[j]).numer);b=build((gs[i]-gs[j]).numer)
            if not a and not b:
                return 'literal pair duplication for all gaps',bound,bound,dict(cnt)
            cq=poly_gcd(a,b)
            checks.append(('literal duplicate pair',cq))

    bad=[A.delta,A.H,A.B,A.g4,A.g4-A.h,m,u,k0,A.q,3*u-2,A.ht]
    checks+= [('scalar guard',ff) for f in bad for ff in (f.numer,f.denom)]
    seen=0
    for lab,b in checks:
        if lab=="scalar guard":b=build(b)
        if not b:
            return 'all gaps violate '+lab,bound,bound,dict(cnt)
        if len(b)==1:continue
        while seen<bound:
            d=poly_gcd(poly_gcd(b,F),G)
            if len(d)<=1:break
            seen+=len(d)-1
            cnt[lab]+=len(d)-1
            F,mm=divmod_coeff(F,d);G,nn=divmod_coeff(G,d)
            assert not mm and not nn
        if seen>=bound:
            return 'all bad gcd factors',bound,seen,dict(cnt)
    return 'needs more',bound,seen,dict(cnt)


if __name__=='__main__':
    tally=Counter()
    co=Path(__file__).with_name('resultant_factors.json')
    for j,k,ls in json.loads(co.read_text()):
        for cs,e in ls:
            d=len(cs)-1
            if d==172:continue
            out=recover(K(A.fs[j]).numer,K(A.gs[k]).numer,fmpq_poly([fmpq(c) for c in cs]))
            assert out[0] in ('third pair at exhausted first clock','all bad gcd factors'),out
            assert out[1]==out[2]
            tally.update(out[3])
            print(j,k,d,e,cs[0],out,flush=True)
    assert tally==Counter({'scalar guard':8,'literal duplicate pair':25,'third pair at exhausted first clock':4}),tally
    print('every smaller regular cross-fed factor is excluded')

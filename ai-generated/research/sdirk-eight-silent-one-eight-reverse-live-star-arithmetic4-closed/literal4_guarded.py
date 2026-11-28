"""Licensed characteristic-zero fourth support, then all local actual fibres."""
from literal4_projection import projections
from literal4_model import model
from literal4_fibers import use_s
from literal4_aux import rational
from check_star_arithmetic67 import exact_support,mono,pol_mod,s_coeffs,gfiber
from star4_guarded_fibers import Field,gpoly,modQ
from silent8_fibers import sfactors
from star4_actual_fifth import Bfield,gcdp,trim,nmod_poly,sv
from regular_star_projection import red,Co
from flint import fmpz_poly,fmpq_poly
from ast import literal_eval
from pathlib import Path
from collections import Counter

pr=65537;tt=2040
gn=('gamma','early_a','early_b','anchor','s_eq_a','s_eq_b',
        'x_eq_silent','x_eq_a','x_eq_b','quintic','terminal_h')

def all_small(M,U,p=pr,t=tt):
    A,B=projections()
    R=modQ(M,p)
    assert R.degree()==M.degree() and R.leading_coefficient()==1
    Q=nmod_poly([1],p);ok=Counter();errs=[]
    for P,e in R.factor()[1]:
        Q*=P**e
        K=Bfield(P,p,t);g=K(nmod_poly([0,1],p))
        W=pol_mod(U,K,p)
        assert W and len(W)==len(U) and W[-1]==1
        for F in (A,B):W=gcdp(W,gfiber(F,K))
        if len(W)==1:ok['no_s']+=1;continue
        for S,k in sfactors(W,K):
            try:n,s=use_s(K,g,S,p,t)
            except (ArithmeticError,ValueError,ZeroDivisionError,AssertionError) as ex:
                n,s='arithmetic_fail',str(ex)
            if n not in ('no_gap','no_true_fifth'):
                hs={}
                for name,G in zip(gn,model()[5]):
                    d=len(gcdp(S,sv(G,K,g,p,t)))-1
                    if d:hs[name]=d
                errs.append((P.degree(),len(S)-1,n,s,hs))
            else:ok[n]+=1
    assert Q==R
    return ok,errs

PLAN={
    (3,10):(31,9,1,{'no_s':3}),
    (45,1):(33,3,1,{'no_s':2}),
    (9,42):(33,6,6,{'no_s':2}),
    (21,108):(33,3,9,{'no_s':2}),
    (7,1):(33,6,1,{'no_s':2}),
    (3,24):(33,None,0,{'no_gap':2}),
    (5,3):(33,10,3,{'no_s':3}),
    (46,3):(33,10,3,{'no_s':5}),
}

def one(M,e):
    A,B=projections();guards=model()[5]
    K=Field(fmpq_poly(M))
    D,E=[trim([K(fmpq_poly(L)) for L in s_coeffs(F)]) for F in (A,B)]
    Q=mono(min((W for W in (D,E) if W),key=len))
    s0,idx,n,count=PLAN[M.degree(),e]
    assert len(Q)==s0+1
    if n:
        G=trim([K(gpoly(Z)) for Z in Co(rational(guards[idx]),1)])
        Q=exact_support(Q,G,K,n)
    C,Bad=all_small(K.M,Q)
    assert len(Q)==s0+1-n and not Bad and C==count,(Bad,C,count)
    return C

def loads():
    for line in Path('literal4-cover-plan.txt').read_text().splitlines():
        e,text=line.split(' ',1);k=text.index(']')
        j=literal_eval(text[:k+1]);a=list(map(int,text[k+1:].split()))
        yield fmpz_poly(a),int(e),j

def main():
    total=Counter()
    for M,e,label in loads():
        C=one(M,e)
        total.update(C)
        print('literal4 whole exact guarded branch',M.degree(),e,dict(C),flush=True)
    assert total=={'no_s':19,'no_gap':2}
if __name__=='__main__':main()

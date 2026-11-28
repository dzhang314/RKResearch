from projection_residual import *
from field_fmpq import Field
from places import spec
from flint import nmod_poly
from sympy import isprime
SITES={23:(997,650),8:(1031,655),12:(997,471),4:(997,961)}
def certify(mode):
    R,rows,eq,guards,lin,q,base,pure=linear_drop(mode)
    c0,c1,c2=cf(eq[0])
    fs=R.factor()[1]
    assert [(f.total_degree(),e) for f,e in fs]==[(23,2),(8,5),(12,5),(4,15)]
    for f,e in fs:
        dg=f.total_degree();K=Field(f)
        p,h=SITES[dg]
        hr=spec(f,p,1,var=0)
        assert isprime(p) and hr.degree()==dg and hr(h)==0 and hr.derivative()(h)
        # One stable leading a coefficient suffices for integrality of a at a place of Q(H).
        aa=[spec(x,p,h) for x in rows]
        assert aa[0].degree()==c2.degrees()[1] and aa[0].degree()>0
        gg=aa[0]
        for g in aa[1:]:gg=gg.gcd(g)
        assert gg.degree()==(3 if dg==4 else 1)
        GUARD={23:q,8:ip(N(a/2).n),12:ip(N(a/2).n),4:ip(D(a/2).n)}[dg]
        A=K.gcd(K.trans(c2),K.trans(GUARD))
        print('start closure',mode,dg,'exact guard gcd',len(A)-1,'mod max',gg.degree(),flush=True)
        assert len(A)-1==gg.degree()
        for i,x in enumerate(rows[1:]):
            assert not K.divrem(K.trans(x),A)[1]
        print(mode,dg,'all exact candidates forbidden by guard found, rank degree',gg.degree(),flush=True)
if __name__=='__main__':
    for mode in CASES:certify(mode)
    print('both genuine degree-one projections closed',flush=True)

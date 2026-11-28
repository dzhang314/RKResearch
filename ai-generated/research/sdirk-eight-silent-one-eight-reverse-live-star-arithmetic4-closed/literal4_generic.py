"""Whole exact rational quotient, retaining every arbitrary ordinary fifth fibre."""
from literal4_fibers import verify_partial
from flint import nmod_poly
import gzip,sys
sys.set_int_max_str_digits(0)

def main():
    p=65537;t=2040
    with gzip.open('literal4-quotient.gz','rt',encoding='utf-8') as f:
        Q=nmod_poly([int(x)%p for x in f],p)
    assert Q.degree()==4076
    Q*=pow(int(Q.leading_coefficient()),-1,p)
    F=Q.factor()[1]
    P=nmod_poly([1],p)
    for M,e in F:P*=M**e
    assert P==Q
    print('whole rational literal4 exact quotient',Q.degree(),
          'complete local factors',len(F),flush=True)
    C,B,H=verify_partial(Q,p,t)
    assert not B and C=={'no_gap':27,'no_true_fifth':4},(C,B,H)
    print('literal4 complete generic tail and true fifth replay',dict(C),flush=True)

if __name__=='__main__':main()

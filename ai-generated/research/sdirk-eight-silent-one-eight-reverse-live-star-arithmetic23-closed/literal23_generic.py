"""All retained actual orientation components of exact degree-8194 norm quotient."""
from flint import nmod_poly
import gzip,sys
from literal23_cover_probe import orient_mod
from literal23_fibers import verify_partial
sys.set_int_max_str_digits(0)

def main():
    p=65537;t=2040
    with gzip.open('literal23-norm-quotient.gz','rt',encoding='utf-8') as f:
        Q=nmod_poly([int(l)%p for l in f],p)
    assert Q.degree()==8194
    U=orient_mod(p,t);assert U.degree()==6705
    Z=Q.gcd(U);assert Z.degree()==4097
    R=nmod_poly([1],p)
    F=Z.factor()[1]
    for M,e in F:R*=M**e
    assert R==Z
    print('whole exact quotient residues',Q.degree(),Z.degree(),
          'complete aligned factor count',len(F),flush=True)
    ok,bad,h=verify_partial(Z,p,t)
    assert not bad and ok=={'no_gap':25,'no_true_fifth':4},(ok,bad,h)
    print('complete exact quotient passed valid terminal nodal and fifth gates',dict(ok),flush=True)

if __name__=='__main__':main()

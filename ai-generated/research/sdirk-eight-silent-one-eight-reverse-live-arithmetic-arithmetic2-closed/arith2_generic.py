"""All retained actual orientation components of exact degree-8142 norm quotient."""
from flint import nmod_poly
import gzip,sys
from arith2_cover_probe import orient_mod
from arith2_fibers import verify_partial
sys.set_int_max_str_digits(0)

def main():
    p=65537;t=2040
    with gzip.open('arith2-quotient.gz','rt',encoding='utf-8') as f:
        Q=nmod_poly([int(l)%p for l in f],p)
    assert Q.degree()==8142
    U=orient_mod(p,t);assert U.degree()==6708
    Z=Q.gcd(U);assert Z.degree()==4071
    R=nmod_poly([1],p)
    F=Z.factor()[1]
    for M,e in F:R*=M**e
    assert R==Z
    print('whole exact quotient residues',Q.degree(),Z.degree(),
          'complete aligned factor count',len(F),flush=True)
    ok,bad,h=verify_partial(Z,p,t)
    assert not bad,(bad,h)
    print('complete exact quotient passed valid terminal nodal and fifth gates',dict(ok),flush=True)

if __name__=='__main__':main()

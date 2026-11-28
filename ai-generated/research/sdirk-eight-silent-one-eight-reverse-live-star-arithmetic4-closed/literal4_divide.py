"""Independent exact integer product cover after the full rational diagonal."""
from pathlib import Path
from ast import literal_eval
from flint import fmpz_poly,nmod_poly
import gzip,sys
sys.set_int_max_str_digits(0)

def src():
    for l in Path('literal4-cover-plan.txt').read_text().splitlines():
        e,text=l.split(' ',1);j=text.index(']')
        lab=literal_eval(text[:j+1]);P=fmpz_poly(list(map(int,text[j+1:].split())))
        yield P,int(e),lab

def main():
    A=fmpz_poly()
    with gzip.open('literal4-diagonal.gz','rt',encoding='utf-8') as f:
        for i,l in enumerate(f):
            a=int(l)
            if a:A[i]=a
    assert A.degree()==7029
    P=fmpz_poly([1]);F=list(src())
    assert sorted((M.degree(),e) for M,e,l in F)==[(3,10),(3,24),(5,3),(7,1),(9,42),(21,108),(45,1),(46,3)]
    for M,e,L in F:P*=M**e
    assert P.degree()==2953
    for p in (1129,65537):
        B,C=[nmod_poly([int(x)%p for x in q],p) for q in (A,P)]
        assert C and not B%C
    Q,E=divmod(A,P)
    assert not E and Q.degree()==4076
    print('exact literal4 full product cover',Q.degree(),[(M.degree(),e) for M,e,l in F],flush=True)
    with gzip.open('literal4-quotient.gz','wt',encoding='utf-8') as f:
        f.writelines(str(a)+'\n' for a in Q)

if __name__=='__main__':main()

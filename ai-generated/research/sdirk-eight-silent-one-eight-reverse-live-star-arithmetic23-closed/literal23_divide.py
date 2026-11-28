"""Exact thin-process norm factor division; all model caches are separate."""
from pathlib import Path
from ast import literal_eval
import gzip,sys,gc,ctypes
from flint import fmpz_poly,nmod_poly
sys.set_int_max_str_digits(0)

def load():
    for l in Path('literal23-cover-plan.txt').read_text().splitlines():
        e,k,text=l.split(' ',2);j=text.index(']')
        label=literal_eval(text[:j+1]);A=list(map(int,text[j+1:].split()))
        yield fmpz_poly(A),int(e),int(k),label

def main():
    O=fmpz_poly()
    with gzip.open('lit23-norm-primitive.gz','rt',encoding='utf-8') as f:
        for i,l in enumerate(f):
            a=int(l)
            if a:O[i]=a
    assert O.degree()==13410
    R=fmpz_poly([1]);F=list(load())
    for M,e,n,lab in F:R*=M**e
    assert R.degree()==5216
    for p in (1129,65537):
        OM,RM=(nmod_poly([int(a)%p for a in w],p) for w in (O,R))
        assert RM and not OM%RM
    Q,E=divmod(O,R)
    assert not E and Q.degree()==8194
    del O,R,E;gc.collect()
    try:ctypes.CDLL('libc.so.6').malloc_trim(0)
    except Exception:pass
    print('literal23 exact completely divided norm',Q.degree(),[(M.degree(),e,n) for M,e,n,w in F],flush=True)
    with gzip.open('literal23-norm-quotient.gz','wt',encoding='utf-8') as f:
        f.writelines(str(a)+'\n' for a in Q)

if __name__=='__main__':main()

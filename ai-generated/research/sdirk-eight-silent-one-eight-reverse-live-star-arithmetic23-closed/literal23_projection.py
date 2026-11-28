"""Exact characteristic-zero two scalar projections for actual silent two."""
from literal23_model import model
from regular_star_projection import remove
from small_crt import small_resultant
from functools import lru_cache
from time import perf_counter

@lru_cache(None)
def projections():
    F,G,P,Cross,N,guards,*_=model()
    out=[]
    for name,A,B in [('actual_tail_affine',F,G),('actual_affine_and_nodal',G,N)]:
        t0=perf_counter()
        R=small_resultant(A,B)
        X,c=remove(R,guards)
        assert X
        print('literal silent two exact projected',name,R.degrees(),X.degrees(),c,
              round(perf_counter()-t0,2),flush=True)
        out.append(X)
    assert [x.degrees() for x in out]==[(0,27,96,1),(0,45,136,1)]
    return out

if __name__=='__main__':projections()

"""Independent exact rational scalar projections for actual silent physical fourth."""
from literal4_model import model
from regular_star_projection import red,remove,con,t
from small_crt import small_resultant
from silent8_diag import primitive
from functools import lru_cache
from time import perf_counter

@lru_cache(None)
def projections():
    F,G,P,C,N,guards,*_=model()
    r=[]
    for name,A,B,ds in [('tail_affine',F,G,(33,96)),('affine_nodal',G,N,(43,136))]:
        t0=perf_counter()
        Q=small_resultant(A,B)
        R,p=remove(Q,guards)
        if R== -con(R): R=red(2*t*R)
        assert R==con(R) and R.degrees()[1:3]==ds
        W,h=primitive(R)
        print('actual literal four exact rational projection',name,Q.degrees(),R.degrees(),p,
              'extra strict power',h,W.degrees(),round(perf_counter()-t0,2),flush=True)
        r.append(W)
    return r

if __name__=='__main__':projections()

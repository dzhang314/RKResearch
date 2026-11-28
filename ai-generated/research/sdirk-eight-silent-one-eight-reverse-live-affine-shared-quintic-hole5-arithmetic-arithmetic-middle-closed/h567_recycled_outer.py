"""Bounded split exact CRT with a single worker recycled in small batches."""
from functools import lru_cache
from multiprocessing import get_context,get_all_start_methods
from time import perf_counter
from resource import getrusage,RUSAGE_SELF
from sympy import nextprime,sqrt_mod
from h54_split_outer import geo_image,compiler,exact_outer as direct
from small_crt import int_input,image
from regular_star_projection import C

W=None

def work(task):
    p,z,indep=task
    A,B,cap,degree=W
    G=geo_image(A,B,p,z,cap,degree)
    if G is None or indep:
        G0=image(A,B,p,z,cap,degree)
        if G is not None:assert G==G0
        G=G0
    return p,G,getrusage(RUSAGE_SELF).ru_maxrss

def exact_outer(P,Q):
    if not compiler() or 'fork' not in get_all_start_methods():return direct(P,Q)
    s,t=P.degrees()[0],Q.degrees()[0]
    assert s and t and P.degrees()[1]==Q.degrees()[1]==0
    m=s*Q.degrees()[2]+t*P.degrees()[2]
    cap=(m,0);degree=(s,t)
    A,B=int_input(P),int_input(Q)
    bound=A[2]**t*B[2]**s
    global W
    W=(A[:2],B[:2],cap,degree)
    M=1;prime=2**60;n=0;start=perf_counter()
    cs=[[0]*(m+1) for _ in range(2)]
    with get_context('fork').Pool(1,maxtasksperchild=8) as pool:
        while M<=2*bound:
            jobs=[]
            for _ in range(8):
                prime=int(nextprime(prime))
                while prime%8!=7:prime=int(nextprime(prime))
                z=pow(2,(prime+1)//4,prime)
                assert z*z%prime==2
                jobs.append((prime,z,n==0 and not jobs))
            for p,R,rss in pool.imap(work,jobs,chunksize=1):
                if R is None:continue
                inv=pow(M,-1,p)
                cs=[[v+M*((x-v)*inv%p) for v,x in zip(Pv,Rv)] for Pv,Rv in zip(cs,R)]
                M*=p;n+=1
                if n%24==0:print('recycled split exact checkpoint',n,round(perf_counter()-start,2),'worker KiB',rss,flush=True)
                if M>2*bound:break
        p=65537;z=int(sqrt_mod(2,p));assert z*z%p==2
        pp,R,rss=pool.apply(work,((p,z,True),))
        assert pp==p and R
    W=None
    assert M>2*bound
    cs=[[v if 2*v<M else v-M for v in Pv] for Pv in cs]
    assert all(abs(v)<=bound for Pv in cs for v in Pv)
    assert all((v-x)%p==0 for V,S in zip(cs,R) for v,x in zip(V,S))
    print('recycled split exact outer',s,t,m,n,bound.bit_length(),round(perf_counter()-start,2),flush=True)
    return C.from_dict({(0,0,j,tt):v*2**tt for tt,V in enumerate(cs) for j,v in enumerate(V) if v})

"""Smaller exact nodal-leading auxiliary norm for a product-cover identity."""
from arith_silent8_crt import model
from arith_silent8_diagonal import images
from fast_outer_interpolate import fast_mod_images
from arith_star_diagonal import int_input
from regular_star_projection import g,Co,red,remove
from flint import fmpz_poly
from sympy import nextprime
from functools import lru_cache
from time import perf_counter

@lru_cache(None)
def small_guard():
    D,J,F,N,C,H,delta,dat=model()
    # The auxiliary polynomial is only used for an exact cover split;
    # it supplies no candidate restriction or wholesale root deletion.
    h5=Co(N,0)[-1]
    H5,_=remove(h5,[g])
    P,Q=map(int_input,(J,H5))
    s0,g0=J.degrees()[1:3]
    s1,g1=H5.degrees()[1:3]
    cap=s0*g1+s1*g0
    bound=P[2]**s1*Q[2]**s0
    coef=[[0]*(cap+1) for _ in range(2)]
    p=2**60;M=1;n=0;start=perf_counter()
    assert cap==1123 and bound.bit_length()==4446
    print('auxiliary nodal-leading cap/bound',cap,bound.bit_length(),flush=True)
    while M<=2*bound:
        p=int(nextprime(p))
        if p%8!=7:continue
        z=pow(2,(p+1)//4,p)
        rr=fast_mod_images(P[:2],Q[:2],p,z,(g0,s0,g1,s1))
        if rr is None:rr=images(P[:2],Q[:2],p,z,cap,(s0,s1))
        if rr is None:continue
        mi=pow(M,-1,p)
        coef=[[v+M*((x-v)*mi%p) for v,x in zip(vv,ww)] for vv,ww in zip(coef,rr)]
        M*=p;n+=1
    coef=[[v if 2*v<M else v-M for v in t] for t in coef]
    assert all(abs(v)<=bound for t in coef for v in t)
    rr=images(P[:2],Q[:2],1129,406,cap,(s0,s1))
    assert all((v-r)%1129==0 for a,b in zip(coef,rr) for v,r in zip(a,b))
    U,V=map(fmpz_poly,coef)
    K=U*U-2*V*V
    assert K
    h=min(i for i,v in enumerate(K) if v)
    K=K.right_shift(h); K=K//K.content()
    assert K.degree()==2042 and n==75
    print('auxiliary exact small norm',K.degree(),n,round(perf_counter()-start,2),flush=True)
    return K

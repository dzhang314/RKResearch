"""Exact old early-rank guard fiber of the regular actual eighth silence."""
from functools import lru_cache
from h58_star_projection import main_front,model,crt,remove,gpoly,Co
from unequal_finite import ExField,gcdp,divp
from aq_modular import Bfield,lcmo,nmod_poly

@lru_cache(None)
def affine_rank_projection():
    P=main_front()
    gs=model(True)[6]
    R=crt(P,gs[1],'fifth hole exact affine early-rank locus')
    Q,ex=remove(R,tuple(h for h in gs if h.degrees()[0]==0))
    G=gpoly(Q).monic()
    assert (R.degrees()[2],Q.degrees()[2],G.degree())==(60,30,30)
    assert ex==[18,3,0,0] and not G.b
    print('affine exact rank locus',R.degrees(),Q.degrees(),ex,G.degree(),flush=True)
    return G

def affine_rank_cut(M,P,Q):
    G=affine_rank_projection()
    trial,power=M,0
    while True:
        d,rem=trial.div(G)
        if rem:break
        assert d*G==trial
        trial=d
        power+=1
    assert power==4 and trial.degree()==372
    N=ExField(G)
    rank=[N(gpoly(h)) for h in Co(model(True)[6][1])]
    pe=[N(gpoly(h)) for h in Co(P)]
    z=gcdp(pe,rank)
    assert len(z)==2 and z[-1]==1
    assert not divp(rank,z)[1]
    k=0
    while True:
        n,rem=divp(pe,z)
        if rem:break
        assert n
        pe=n;k+=1
    assert k==1 and len(pe)==5
    j=pe[-1].inv()
    mon=[(v*j).v for v in pe]
    assert len(mon)==len(pe)
    # The exact discarded Y factor implies rank loss. The remaining monic Y
    # is lifted through a separate complete degree-preserving local check.
    p,t=1129,203
    Bs=Bfield(nmod_poly([0,1],p),p,t)
    redG=Bs.cast(G)
    assert redG.degree()==G.degree() and redG.leading_coefficient()==1
    fac=redG.factor()[1]
    prod=nmod_poly([1],p)
    for q,e in fac:
        prod*=q**e
        B=Bfield(q,p,t)
        T=[B(r) for r in mon]
        assert T[-1]==1
        U=lcmo(B,Co(Q))
        assert gcdp(T,U)==[B(1)]
    assert prod==redG and len(fac)==3
    print('affine exact rank guard fiber',G.degree(),power,'removed Y multiplicity',k,
          'remaining Y degree',len(mon)-1,'all unit components',len(fac),'retained',trial.degree(),flush=True)
    return trial

"""Verified integer product cover, without large-polynomial irreducibility."""
from arith_silent8_diagonal import exact_diagonal
from nodal_guard_aux import small_guard
from flint import fmpz_poly

# Indices of exact factors of the smaller auxiliary norm, used only
# to propose the following exact integer product. No auxiliary equation
# is ever imposed on a true candidate.
POWERS={(48,2):1,(24,3):15,(60,3):12,(18,4):8,(42,12):42,(4,18):72,(8,24):102}

def verified_cover():
    A,B=exact_diagonal()
    N=A*A-2*B*B
    assert N.degree()==9248
    N=N//N.content()
    K=small_guard()
    unit,F=K.factor()
    check=fmpz_poly([unit]);out=[];S=fmpz_poly([1]);tags=set()
    for P,e in F:
        check*=P**e
        k=(P.degree(),e)
        if k in POWERS:
            tags.add(k);n=POWERS[k]
            S*=P**n
            out.append((P,n))
    assert check==K and tags==set(POWERS)
    Q,R=divmod(N,S)
    assert not R and Q.degree()==5108 and Q*S==N
    print('exact checked whole norm cover',Q.degree(),[(P.degree(),e) for P,e in out],flush=True)
    return [(Q,1),*out]

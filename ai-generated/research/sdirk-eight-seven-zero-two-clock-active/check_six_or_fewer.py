"""Exact six-label exclusion, with no aggregation of the rear tap ratio."""
from check_seven_labels import K,R,X,u,v,a,b,Dside,C

def det(M):
    a,b,c=M
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])

for i,(D,C3) in enumerate(Dside):
 for rear in ('star','arith'):
    w=(2-v) if rear=='star' else 2*v
    s=D-1-w;t=D-1-v
    assert D and len({a,b,s,t})==4
    def I(P):return sum((c*D**j*C(1,j+1) for (j,),c in P.items()),K.zero)
    P3=(X-a)*(X-s)*(X-t)
    m=[I(P3*X**j) for j in range(5)]
    assert det([[m[j+k] for k in range(3)] for j in range(3)]) # >= 6 labels
    P4=P3*(X-b)
    m=[I(P4*X**j) for j in range(4)]
    d=m[0]*m[2]-m[1]*m[1]
    assert d
    o=(m[1]*m[3]-m[2]*m[2])/d
    p=(m[1]*m[2]-m[0]*m[3])/d
    P2=X*X+p*X+o
    assert not I(P4*P2) and not I(X*P4*P2)
    assert C3.evaluate(X,s) and C3.evaluate(X,t)
    assert P2.gcd(C3).degree()==0
    print(i,rear,'ordinary rank 3, two-coefficient pivot nonzero, third-clock gate excludes all 4 candidate labels',flush=True)

"""Fixed ordinary nodal completion: order-eight linear chronology residuals."""
from equal_undetected_front import Nested
from star4_actual_fifth import det,sc,qr,pe,nodal,mul,gcdp,trim
from off8_fibers import cramer

def qsum(K,F):
    return sum(F,K(0))

def divide_root(P,r,K):
    Q,R=qr(P,[-r,K(1)])
    assert not R and Q and Q[-1]==1
    return Q

def extend(K,P):
    if len(P)==2:
        return K,-P[0]/P[1],K
    assert len(P)>2
    U=Nested(sc(P,P[-1].inv()))
    return U,U.gen(),U

def factor_deriv(P,K):
    return [K(j)*a for j,a in enumerate(P[1:],1)]

def lagrange_row(nodes,K):
    ans=[]
    for j,b in enumerate(nodes):
        P=nodal([a for i,a in enumerate(nodes) if i!=j])
        ans.append(sc(P,pe(P,b).inv()))
    return ans

def col_weights(K,Y,g):
    cc=[g*y for y in Y]
    # The first clock is excluded from both actual measures.
    iii=(1,2,3,4,5,6,8,9)
    D=nodal([cc[i] for i in iii]);W=nodal(cc[1:])
    DD=factor_deriv(D,K);WW=factor_deriv(W,K)
    B=[K(0)]*10;Z=[K(0)]*10
    for i in iii:
        Q,R=qr(D,[-cc[i],K(1)])
        assert not R
        B[i]=qsum(K,(K(a)/(j+1) for j,a in enumerate(Q)))/pe(DD,cc[i])
        B[i].inv()
    L=-B[-1]*pe(WW,cc[-1])
    L.inv()
    for i in range(1,10):
        Z[i]=L/pe(WW,cc[i])
    return B,Z

def reverse_core(K,Y,h,g,k,W,Z):
    x=Y[-1];u=x-Y[8];ginv=g.inv()
    cols=[[W[i],W[i]*Y[i],Z[i]] for i in (7,8,9)]
    M=list(map(list,zip(*cols)))
    di=det(M).inv()
    k.inv();u.inv()
    LR=lagrange_row(Y[1:4],K)
    ix=((5,4),(6,4),(6,5))
    free0={v:i for i,v in enumerate(ix)}
    def getA(t):
        A=[[K(0) for j in range(10)] for i in range(10)]
        for i in range(10): A[i][i]=K(1)
        for i in range(1,10): A[i][0]=2*h[i]
        # At the star literal third the coupling to physical two is zero.
        y=Y[3]
        r0=y-1-2*h[3];r1=y*y/2-y-2*h[3]
        A[3][1]=(Y[2]*r0-r1)/(Y[2]-Y[1]);A[3][2]=r0-A[3][1]
        for v,i in free0.items():
            A[v[0]][v[1]]=t[i]
        for j in (4,5,6):
            y=Y[j];w=W[j];z=Z[j]
            rhs=[w*(ginv-y-1),(z+w*(ginv*ginv-y*y-2*y))/2,z*(x-y)/k]
            for col in range(3):
                rhs[col]-=qsum(K,(A[i][j]*([W[i],W[i]*Y[i],Z[i]][col]) for i in range(j+1,7)))
            R=cramer(M,rhs)
            for i,a in zip((7,8,9),R):A[i][j]=di*a
        A[9][7]=Z[7]/(2*u*W[9]);A[8][7]=-W[9]*A[9][7]/W[8]
        A[9][8]=u
        for i in range(4,10):
            y,hi=Y[i],h[i]
            M0=y-1-2*hi-qsum(K,(A[i][j] for j in range(4,i)))
            M1=y*y/2-y-2*hi-qsum(K,(A[i][j]*Y[j] for j in range(4,i)))
            M2=y**3/3-y*y-4*hi/3-qsum(K,(A[i][j]*Y[j]**2 for j in range(4,i)))
            for j,f in enumerate(LR,1):
                A[i][j]=qsum(K,(c*d for c,d in zip(f,(M0,M1,M2))))
        return A
    return getA

def dot(K,L,R):
    return qsum(K,(a*b for a,b in zip(L,R)))

def matrix_multiply(K,A,p):
    return [dot(K,row,p) for row in A]

def residual(K,Y,h,g,W,A):
    ginv=g.inv()
    H=[matrix_multiply(K,A,[y**j for y in Y]) for j in (3,4)]
    def raw(i,j):
        return dot(K,[w*y**i for w,y in zip(W,Y)],H[j-3])-ginv**(i+j+1)/((j+1)*(i+j+2))
    Ah=matrix_multiply(K,A,h)
    # The first three are paid single-inner-bush reads. The fourth is
    # the paid order-seven b C^2 A h combination of four rooted trees.
    return [raw(2,3),raw(2,4),raw(3,3),dot(K,[w*y*y for w,y in zip(W,Y)],Ah)]

def reject_chronology(K,Y,H,g,k):
    W,Z=col_weights(K,Y,g)
    A=reverse_core(K,Y,H,g,k,W,Z)
    A0=A([K(0)]*3)
    R0=residual(K,Y,H,g,W,A0)
    Rs=[]
    for j in range(3):
        A1=A([K(int(i==j)) for i in range(3)])
        Rs.append([r-s for r,s in zip(residual(K,Y,H,g,W,A1),R0)])
    det(list(map(list,zip(*Rs,R0)))).inv()

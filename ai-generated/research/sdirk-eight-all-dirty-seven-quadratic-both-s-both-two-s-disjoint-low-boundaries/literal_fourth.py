"""Exact fourth-site completions of the low/low symmetric disjoint slices."""
import sympy as S
from sympy.polys.rings import ring
def D(x):return -2+x+4*x*x-x**3
def kap(x):return 1+2*x-x*x
def N(x):return (1+4*x-4*x*x)*D(x)+4*x*x*(3*x-2)
def exact(K,a,H,mode):
    W,w=ring('w',K)
    z=K.zero
    h=H/2;m=1+h
    y=w+h
    p=2*a if mode=='A3A3' else 2-a
    q=H-p;t=H-a
    fs=kap(a)/2
    g=N(a)/(2*D(a)) if mode=='A3A3' else fs
    l=lambda f,x:f.evaluate(w,x)
    L3=w**3-3*m*m*w/5
    L4=w**4-6*m*m*w*w/7+3*m**4/35
    d=p-h;x=a-h
    R=K.one/2+(fs-K.one/2)*(w*w-h*h)/(x*x-h*h)
    C=2*l(L4,h)+(l(L4,x)/fs-2*l(L4,h))*(w*w-h*h)/(x*x-h*h)
    assert g and fs and l(L4,d) and l(L4,z) and g-l(R,d)
    B=(l(L4,d)-g*l(C,d))/(g*(g-l(R,d)))
    assert B
    A=C-B*R
    T2=W.zero
    spans=[(z,K.one/2),(a,fs),(p,g)]
    for x0,b in spans:
        P=W(b)
        for x1,c in spans:
            if x1!=x0:P=P*(y-x1)/(x0-x1)
        T2+=P
    # x=y+1; translation applied to the known genuine degree-two interpolation.
    w0=-(K.one+h);u0=l(T2,w0);u1=l(T2.diff(w),w0);u2=T2[(2,)]
    X=y+1
    J=u0*X+u1*X*X/2+u2*X**3/3
    k=kap(a)
    La=1+(X-1)/k
    Delta=W(K.convert(S.QQ(4,3)))+2*(k+1)*(X-1)/(3*k)
    C4=1-La+u1+u2*Delta
    N4=T2-J
    gother=-l(L4,d)/(B*g)
    assert gother
    bad=[bool(l(C4,e)*gother-l(N4,e)) for e in (d,-d)]
    A2,g0=ring('g',K)
    U0=A2(l(L4,z))-g0*(l(A,z)+B*g0)
    D0=A2(l(C4,z))*g0-l(N4,z)
    bad.append(U0.gcd(D0)==A2.one)
    return bad

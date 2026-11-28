"""Locate exact fixed-place exclusion in the two-overlap noncentral A/A case."""
from flint import nmod_poly as NP
import sympy as S
uv=S.Symbol('u')
q=81*uv**9-891*uv**8+3411*uv**7-4659*uv**6-733*uv**5+4378*uv**4+940*uv**3-992*uv**2-432*uv-48
F=S.Poly(q,uv)
assert F.is_irreducible
def dd(u):return -2+u+4*u*u-u**3
def kk(u):return 1+2*u-u*u
def nn(u):return (1+4*u-4*u*u)*dd(u)+4*u*u*(3*u-2)
def ip(ww,pts,p):
    A=NP([],p)
    for x,y in pts:
        a=NP([y],p)
        for d,c in pts:
            if d!=x:a=a*(ww-d)*pow((x-d)%p,-1,p)
        A+=a
    return A
def one(p,u):
    i=lambda x:pow(x%p,-1,p)
    R0=lambda n:NP([n%p],p)
    w=NP([0,1],p)
    h=3*u*i(2)%p;d=u*i(2)%p;m=(h+1)%p
    D=dd(u)%p;N=nn(u)%p;k=kk(u)%p
    if not (u*(u-2)*(3*u-2)*m*D*N*k)%p:return 'front'
    L=w**4-6*m*m*i(7)*w*w+3*m**4*i(35)
    ld=int(L(d));lh=int(L(h))
    b0=(d*d-3*m*m*i(5))%p
    if not (ld*b0)%p:return 'anchor'
    eta=(ld*i(b0)+6*m*m*i(7)-d*d)%p
    E=w*w-eta
    roots=E.roots()
    if len(roots)!=2:return 'unsplit'
    f1=k*i(2)%p; f2=N*i(2*D)%p
    beta=(-ld*i(f1*f2))%p
    rs=[]
    for e,n in roots:
        e=int(e)
        if not (e*(e-h)*(e+h)*(e-d)*(e+d))%p:return 'D collision'
        l=(h+e)*i(h-e)%p
        B=beta*i(l)%p
        R=w*(w+e)*i(2*h*(h-e))
        assert R(-h)==i(2) and R(h)==l*i(2)%p
        A=ip(w,[((-h)%p,(2*lh-B*i(2))%p),
                ((-d)%p,(-B*(f1+l*f2))%p),
                (d,(-B*(f2+l*f1))%p)],p)
        assert A(h)==(2*lh*i(l)-B*l*i(2))%p
        J,r=divmod(L-R*(A+B*R),w*w-h*h)
        assert not r
        if J.degree()!=2:return 'J degree'
        alpha=(3*u-2)*i(D)%p
        a=(1-alpha*u)%p;c=(alpha-i(2))%p
        ay=(i(2)-a+c)%p;by=(a-2*c)%p
        x=w+1+h
        T=ay+by*x+c*x*x
        JT=ay*x+by*i(2)*x*x+c*i(3)*x**3
        La=1+(x-1)*i(k)
        De=4*i(3)+2*(k+1)*(x-1)*i(3*k)
        C4=1-La+by+c*De
        N4=T-JT
        Sg=J.gcd(C4*R-N4).degree()
        U=R0(int(L(e)))-w*(int(A(e))+B*w)
        Dg=U.gcd(int(C4(e))*w-int(N4(e))).degree()
        if U.degree()!=2:return 'U degree'
        rs.append((e,Sg,Dg))
    return rs
def run():
    h=3*uv/2
    d=uv/2
    m=h+1
    D=dd(uv)
    f1=kk(uv)/2
    f2=nn(uv)/(2*D)
    L=lambda z:z**4-6*S.Rational(1,7)*m*m*z*z+3*S.Rational(1,35)*m**4
    assert S.cancel(4*L(h)*f1*f2-L(d)*(1+6*(f2-f1))+2*uv*uv*q/(35*D))==0
    w=S.Symbol('w')
    slope=(d*d-3*S.Rational(1,5)*m*m)/L(d)
    eta=1/slope+6*S.Rational(1,7)*m*m-d*d
    assert S.cancel(w**3-3*S.Rational(1,5)*m*m*w-slope*w*L(w)
                    +slope*w*(w*w-d*d)*(w*w-eta))==0
    p,u=23,5
    assert S.isprime(p)
    rr=NP(list(map(int,reversed(F.all_coeffs()))),p)
    assert rr.degree()==9 and not rr(u) and rr.derivative()(u)
    rs=one(p,u)
    assert rs==[(8,0,0),(15,0,0)] or rs==[(15,0,0),(8,0,0)]
    print('noncentral gap degree nine; both e residues at 23,5 excluded',flush=True)
if __name__=='__main__':run()

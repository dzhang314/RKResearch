"""Exact origin-root polynomial for the F29 lift with g=6,R=15,d=26."""
import sympy as S

x=S.Symbol("x")
c=S.Symbol("c")
g,R,d=map(S.Integer,(6,15,26))
def I(f):
    f=S.Poly(f,x)
    return S.cancel(sum(a/(i[0]+1) for i,a in f.terms()))
def J(f):
    f=S.Poly(f,x)
    return sum(a*x**(i[0]+1)/(i[0]+1) for i,a in f.terms())
def coefficients():
    M=x*x*(x-c)**2
    JM=J(M)
    W=(1-x)*(x-g)*(x-R)*JM
    h=S.cancel(I(x*W)/I(W))
    S4=(1-x)*(x-g)*(x-h)*(x-R)
    f=S.cancel(I(S4*x*M)/I(S4*M))
    om=210*c**3-336*c*c+168*c-28
    T=(x-f)*(x-g)*(x-h)
    k=I(x*(x-1)*(x-c)**2*(x-R)*T)
    j=I(S4*(x-f)*x*(x-c)*(1+om*x))
    A1=S.factor(j+(1-2/c)*k)
    return h,f,k,j,A1
if __name__=="__main__":
    h,f,k,j,a=coefficients()
    print("h =",h)
    print("f =",f)
    n,d=S.fraction(a)
    print("origin numerator factors:",S.factor_list(n,c))
    print("origin denominator degree:",S.degree(d,c))
    for b,m in S.factor_list(n,c)[1]:
        print("factor degree, mod29 value and derivative at c=2:",
              S.degree(b,c),b.subs(c,2)%29,S.diff(b,c).subs(c,2)%29)

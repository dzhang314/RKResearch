"""Exact 29-adic coefficient receipt for the two necessary nonlinear minors."""
from reciprocal import F, S, ring, t, scheme, DomainMatrix
from spectrum import mul,nodes,moment,val,L4

p=29
rr=lambda z:int(z.p)*pow(int(z.q),-1,p)%p
cc,gg,R=map(F,["1/2","2/3","1/4"])
D,C=scheme(cc,gg,R)
h,f=D["h"],D["f"]
CL=val([F(0)]+L4(),cc)
hu=moment(mul(mul([F(1),F(-1)],nodes([gg,R])),D["JM"]))
fu=moment(mul(mul([F(1),F(-1)],nodes([gg,h,R])),D["M"]))
def frac(x):return S.Rational(x.numerator,x.denominator)
guards=[rr(frac(x)) for x in [hu,fu,CL,f*(f-cc),D["k"]+D["ell"]]]
assert guards==[4,28,20,2,2]
assert [rr(frac(z)) for z in [cc,gg,R,h,f]]==[15,20,22,14,8]
dp=S.Poly(ring.to_sympy(D["Delta"]),t,domain=S.QQ)
dc=[rr(a) for a in dp.all_coeffs()]
assert dc==[21,22,19] and all(rr(dp.eval(i)) for i in range(29))
print("29-adic input and reconstruction units:",guards,"pivot:",dc)
for i,w,z in ((0,32,[2,7,13]),(6,35,[0,24])):
    P=S.Poly(ring.to_sympy(DomainMatrix([[c[j] for c in C] for j in range(7) if j!=i],
                                 (6,6),ring).det()),t,domain=S.QQ)
    assert P.degree()==w
    vals=[rr(P.eval(a)) for a in range(29)]
    roots=[a for a,x in enumerate(vals) if not x]
    assert roots==z
    coef=[rr(q) for q in P.all_coeffs()]
    if i==6: assert coef[0]==28
    print("minor omitting",i,"degree",w,"roots",roots,"coefficients",coef)

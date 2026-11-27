"""Exact eight-node scalar geometry with both two-port clocks and an AP reverse start."""
from fractions import Fraction
from itertools import permutations
from pathlib import Path
import sys
port_dir=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'real-sdirk13-forward-ports'
sys.path.insert(0,str(port_dir))
from check_two_ports import I, ev, der, plus, sc, solve, tr, around, sign_bracket, cert_roots, cert_ports
Z=I.val(0); O=I.val(1)
_,[z,v,w],_=cert_ports(cert_roots())
# Physical reflected label of the large port coincides with the first, actual reverse clock.
gamma=1/(1+v)
h=1-gamma*w
P=[[O],[I.val(-1),I.val(2)]]
def conv(p,q):
    v=[Z]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):v[i+j]=v[i+j]+a*b
    return v
for k in range(2,9):
    P.append(sc(Fraction(1,k),plus(sc(2*k-1,conv(P[-1],P[1])),sc(1-k,P[-2]))))
def det(A):
    m=len(A);b=Z
    for p in permutations(range(m)):
        eps=(-1)**sum(p[i]>p[j]for i in range(m)for j in range(i+1,m))
        v=I.val(eps)
        for i,j in enumerate(p):v=v*A[i][j]
        b=b+v
    return b
def leg_values(x):
    t=2*x-1
    a=[O,t]
    for j in range(2,9):a.append(((2*j-1)*t*a[-1]-(j-1)*a[-2])/j)
    return a
def matrix(d):
    return [leg_values(y)[5:9]for y in [gamma,h,gamma+d,gamma+2*d]]
def deriv(d):
    A=matrix(d);u=A[:];u[2]=[ev(der(P[j]),gamma+d)for j in range(5,9)]
    f=A[:];f[3]=[2*ev(der(P[j]),gamma+2*d)for j in range(5,9)]
    return det(u)+det(f)
_,d,_=around("-0.02880496921399255248824360608086801777914449355387965812986868903639924798385633047553406279052394275789245905393543934973798279950447918792230449362218578846059983306139758201755323337838393181276811588690446601260013266202490486686385","1e-142")
assert det(matrix(I(d.lo,d.lo))).sign()*det(matrix(I(d.hi,d.hi))).sign()==-1
assert deriv(d).sign()
A=matrix(d)[:3]
u=solve([r[:3]for r in A],[[-r[3]]for r in A])
Qh=[r[0] for r in u]+[O]
def eval_h(x,power=0):
    return sum((a*ev(der(P[j]) if power else P[j],x) for j,a in enumerate(Qh,5)),Z)
R=[]
for c in ("-0.583519156178462006588757704796561726540067434794489305115577845006523105941936794289095884662693466898115365213339607646177135895056594731817456075737938727155048320580878487904819046730142062400638623982794210510003220193767634017994",
          "0.3819911002968421708855179867153869959809919610605250152225459147602594652059449374411917321457021161265776647767679481466450897510092756196068894396039693892659294143278852101166724788888330288299633959119840580196048094564298158708869",
          "0.6263697343639524510535811820556709955868779991091462648849745584206296811606345844865668897160423729011905793040212357004392682208345913001589908719428816240425719721541299815193415276982830769834651303984451416531557762153148306864512",
          "0.8355304051979695162118682022471739701270665765293992810892423024265349217925321985328819940139187255969207548359113238390372141790207849712929666553376871358261788811850652316850654916607070069052076688383044489415385519828892112338805"):
    _,b,_=around(c,"1e-120")
    assert eval_h(I(b.lo,b.lo)).sign()*eval_h(I(b.hi,b.hi)).sign()==-1
    assert eval_h(b,1).sign()
    R.append(b)
Y=[R[0],gamma+2*d,gamma+d,gamma,*R[1:],h]
assert all(a.hi<b.lo for a,b in zip(Y,Y[1:]))
def cardinal_weight(i):
    p=[O];q=O
    for j,y in enumerate(Y):
        if i!=j:
            p=conv(p,[-y,O])
            q=q*(Y[i]-y)
    return sum((v/(j+1)for j,v in enumerate(p)),Z)/q
W=[cardinal_weight(i)for i in range(len(Y))]
sg=[t.sign()for t in W];assert all(sg)
assert u[0][0].sign() # H P5 is a nonzero degree-13 quadrature error.
print('8 exact, separated real-algebraic sites on a precision-12 rule.')
print('First reverse actual labels y_3,y_2,y_1 are an arithmetic progression; both forward ports hit y_3 and y_7.')
print('Weight signs:',sg,'; degree-13 quadrature failure certified.')

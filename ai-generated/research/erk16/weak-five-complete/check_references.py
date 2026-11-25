"""Exact common mesh and two crossed-tail reference calculations."""
from fractions import Fraction as F

POINTS = (1, 3, 6, 11, 18, 26, 34, 44, 54, 64, 74, 84, 94, 102, 110, 117, 122, 125, 127)
MASS_DENOMINATOR = 425643294094315542650108828261897814911098830084716100131250000
MASS_NUMERATORS = (
    7814342460740946038962452076987648755614684681221457313792000,
    4685351381346908599620158826884682287277020980078379008000000,
    15592018568332813787561889361221967959072108781593162953079375,
    18371798829007469411027940120405361266792834205990421790720000,
    27465356830788935181174499358384782493848445386944149883562500,
    24427545848317978187064782321083671660786656928557411284752375,
    30996358051620617353037286683523494150404841727706394580592548,
    33628036229450614193353899723312119705056163937683900966131712,
    33272296800004995904814596438679866786986113716667117803133970,
    33137084095092985336873818440930624779421089391831308963721040,
) + tuple(reversed((
    7814342460740946038962452076987648755614684681221457313792000,
    4685351381346908599620158826884682287277020980078379008000000,
    15592018568332813787561889361221967959072108781593162953079375,
    18371798829007469411027940120405361266792834205990421790720000,
    27465356830788935181174499358384782493848445386944149883562500,
    24427545848317978187064782321083671660786656928557411284752375,
    30996358051620617353037286683523494150404841727706394580592548,
    33628036229450614193353899723312119705056163937683900966131712,
    33272296800004995904814596438679866786986113716667117803133970,
)))

def ev(P,x):
    y=0
    for a in reversed(P):
        y=y*x+a
    return y


def add(P,Q):
    n=max(len(P),len(Q))
    return tuple((P[i] if i<len(P) else 0)+(Q[i] if i<len(Q) else 0) for i in range(n))


def scale(c,P):
    return tuple(c*p for p in P)


def mul(P,Q):
    a=[0]*(len(P)+len(Q)-1)
    for i,p in enumerate(P):
        for j,q in enumerate(Q):
            a[i+j]+=p*q
    return tuple(a)


def det3(a,b,c,d,e):
    # The matrix is symmetric Hankel, with anti-diagonals a,b,c,d,e.
    first=mul(a,add(mul(c,e),scale(-1,mul(d,d))))
    second=scale(-1,mul(b,add(mul(b,e),scale(-1,mul(c,d)))))
    third=mul(c,add(mul(b,d),scale(-1,mul(c,c))))
    return add(add(first,second),third)


def check_mesh():
    assert len(POINTS)==len(MASS_NUMERATORS)==19
    assert 0<POINTS[0] and POINTS[-1]<128
    assert all(x<y for x,y in zip(POINTS,POINTS[1:]))
    assert MASS_DENOMINATOR>0 and all(m>0 for m in MASS_NUMERATORS)
    for j in range(20):
        assert (j+1)*sum(w*x**j for x,w in zip(POINTS,MASS_NUMERATORS))==MASS_DENOMINATOR*128**j


def check_negative_tail():
    S=(-1,33,-143,143)
    m=lambda j:F(16,(2*j+1)*(2*j+3)*(2*j+5))
    assert all(sum(c*m(i+j) for i,c in enumerate(S))==0 for j in range(3))
    assert [ev(S,x) for x in (0,F(1,4),F(1,2),1)]==[-1,F(35,64),-F(19,8),32]
    P6=(-5,0,135,0,-495,0,429)
    P7=(0,-35,0,385,0,-1001,0,715)
    m=lambda j:0 if j%2 else F(4,(j+1)*(j+3))
    for n,P in ((6,P6),(7,P7)):
        assert all(sum(c*m(i+j) for i,c in enumerate(P))==0 for j in range(n))
    assert F(ev(P6,-1),429*2**6)==F(1,429)
    assert F(ev(P7,-1),715*2**7)==-F(1,1430)
    assert ev(P6,F(-3,4))+ev(P7,F(-3,4))==-F(55733,4*4096)
    X=[-F(1,4*(j+2))+F(35,32*(j+3))-F(49,64*(j+4)) for j in range(3)]
    assert X==[F(37,768),F(71,1920),F(11,384)]
    assert X[0]*X[2]-X[1]**2==F(93,7372800)>0


def check_positive_tail():
    D=15015
    m=lambda j:F(3,(2*j+1)*(2*j+3))
    assert [D*m(j) for j in range(7)]==[15015,3003,1287,715,455,315,231]
    h=lambda j,mult:(m(j+1),mult*m(j))
    c=[scale(D**2,add(mul(h(1,1),h(j,8)),scale(-1,mul(h(0,1),h(j+1,8)))))
       for j in range(5)]
    assert c==[(0,72144072,0),(-490776,-6870864,-82450368),(-446160,-8610888,-54966912),
               (-360360,-6932640,-37477440),(-288288,-5405400,-26906880)]
    assert det3(*c)==scale(33632965656576,(13,239,-46061,673681,26882856,187002816,276243968))
    assert 4*13*26882856>32000**2 and 4*239*673681>20000**2 and 32000+20000>46061
    assert m(5)/m(4)==F(9,13)>F(3,7) and m(6)/m(5)==F(11,15)>F(3,7)
    J=(-5,135,-495,429)
    Phi=(-35,385,-1001,715)
    assert all(sum(c*m(i+j) for i,c in enumerate(J))==0 for j in range(3))
    assert all(sum(c*m(i+j+1) for i,c in enumerate(Phi))==0 for j in range(3))
    d0,e0=F(13,22),F(9,25)
    assert [ev(J,x) for x in (d0**2,F(1,2),1)]==[F(518891,10307264),-F(61,8),64]
    assert [ev(Phi,x) for x in (e0**2,F(1,5),F(1,2),1,F(4,9),F(49,64))]==[
        -F(17605312,48828125),F(192,25),-F(27,8),64,F(841,729),-F(1602629,262144)]
    assert (F(3,7)-d0*e0)/(d0-e0)==F(831,889)
    assert (1-5*d0*e0)/(d0-e0)==-F(245,889)
    e=F(8,15)
    assert (1-e0**2)/(e-e0)==F(1632,325)>5
    r0,r1=F(2,3),F(7,8)
    assert (1-r0**2)/(r0-e)+(1-r1**2)/(r1-e)==F(25,6)+F(225,328)<5
    assert d0*e==F(52,165)>F(1,4)
    assert (F(3,7)-d0*e)/(5*d0*e-1)==F(131,665)<F(1,5)
    v=lambda A:(A+F(3,7))/(5*A+1)
    assert v(F(1,16))==F(55,147) and F(7,8)**2*v(F(1,16))>F(1,4)
    d=F(16,25)
    assert d*F(1,5)/(d+F(7,16))<F(1,8)
    h=[D*(m(j)+8*m(j+1)) for j in range(6)]
    assert h==[39039,13299,7007,4355,2975,2163]
    c=[625*h[j+1]-256*h[j] for j in range(5)]
    assert c==[-1682109,974831,928083,744495,590275]
    assert det3(*[(n,) for n in c])==(-2356494634004992,)
    assert F(3,7)-d*e==F(229,2625)
    assert 1-5*d*e==-F(53,75) and d-e==F(8,75)
    assert F(229,2625)-F(109,1200)==-F(151,42000)


if __name__=='__main__':
    check_mesh()
    check_negative_tail()
    check_positive_tail()
    print('All 20 exact positive-mesh moments and both crossed-tail reference calculations verified.')

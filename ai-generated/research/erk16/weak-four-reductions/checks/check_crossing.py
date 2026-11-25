from fractions import Fraction as F

# Coefficients ascend; every finite decimal below is an exact rational.
C = {
  'J7': ([-8,252,-2520,11550,-27720,36036,-24024,6435], ['.056 .057','.180 .18025','.352 .353','.547 .548','.734 .735','.885 .886','.977 .978']),
  'L7': ([-8,280,-3080,15400,-40040,56056,-40040,11440], ['.050 .051','.161 .162','.318 .319','.5','.68155 .682','.838 .839','.949 .950']),
  'K7': ([-36,840,-6930,27720,-60060,72072,-45045,11440], ['.088 .089','.226 .227','.399 .400','.585 .586','.759 .760','.896 .897','.979 .980']),
  'J8': ([9,-360,4620,-27720,90090,-168168,180180,-102960,24310], ['.044 .045','.144 .145','.286 .287','.454 .455','.628 .629','.785 .786','.908 .909','.982 .983']),
}

def moment(name,k):
    if name[0] == 'J': return F(1,k+2)
    if name[0] == 'L': return F(1,(k+2)*(k+3))
    if name[0] == 'K': return F(1,k+3)
    raise ValueError(name)

def ev(poly,x):
    s = F(0)
    for a in reversed(poly): s = s*x+a
    return s

for name,(coeff,brackets) in C.items():
    n = len(coeff)-1
    assert len(brackets)==n and coeff[-1]>0
    for k in range(n): assert sum(a*moment(name,j+k) for j,a in enumerate(coeff)) == 0
    end = F(0)
    for i,t in enumerate(brackets,1):
        b=tuple(map(F,t.split()))
        assert end < b[0] <= b[-1] < 1
        if len(b)==1: assert ev(coeff,b[0])==0
        else:
            s=(-1)**(n-i)
            assert s*ev(coeff,b[0])<0<s*ev(coeff,b[-1])
        end=b[-1]

J7=[tuple(map(F,t.split())) for t in C['J7'][1]]
J8=[tuple(map(F,t.split())) for t in C['J8'][1]]
assert all(J8[k][-1] < J7[k][0] and J7[k][-1] < J8[k+1][0] for k in range(7))

def gram(R,S,t):
    R,S,t=map(F,(R,S,t))
    # Integral x^(k+1) (R-x)(S-x)(x-t), k=0,1,2.
    return [R*S*(F(1,k+3)-t*F(1,k+2))-(R+S)*(F(1,k+4)-t*F(1,k+3))+F(1,k+5)-t*F(1,k+4) for k in range(3)]

for R,S,t,g,det in [
    ('1','1','.2',('1/60','1/100','13/2100'),'1/315000'),
    ('1','1','.226',('29/2000','137/15000','403/70000'),'383/6300000000'),
    ('1.8','2.2','.26',('4303/15000','1661/7500','6141/35000'),'2024381/1575000000'),
    ('1.14','1.36','.265',('61433/1500000','89819/3000000','229843/10500000'),'7610749/63000000000000'),
]:
    a,b,c=gram(R,S,t)
    assert (a,b,c)==tuple(map(F,g)) and a>0 and a*c-b*b==F(det)>0

a,b,c=gram('1.5','1.7','.72')
assert (a,b,c)==tuple(map(F,('-2/25','-19/1200','139/105000')))
assert a/9-2*b/3+c==F('157/52500')>0

for a,b,c in [('.051','.226','.226'),('.021','.161','.2'),('.287','.399','.72'),('.319','.454','.72'),('.057','.318','.2'),('.353','.5','.72'),('.023','.24','.2'),('.089','.352','.26'),('.18025','.68155','.265'),('.115','.6','.2')]:
    assert F(a)/F(b)<F(c)
for a,b,c in [('.759','.5','1.5'),('.896','.5','1.7'),('.838','.548','1.5'),('.949','.548','1.7'),('.734','.4','1.8'),('.885','.4','2.2'),('.838','.735','1.14'),('1','.735','1.36')]:
    assert F(a)/F(b)>F(c)
print('All root brackets, orthogonality, threshold Grams, and case inequalities verified exactly.')

from fractions import Fraction as F
J7=[-8,252,-2520,11550,-27720,36036,-24024,6435]
J8=[9,-360,4620,-27720,90090,-168168,180180,-102960,24310]
def ev(p,x):
    z=F(0)
    for a in reversed(p):z=z*x+a
    return z
def ref(e,B):
    e=F(e);v=ev(J8,e)/ev(J7,e);p=list(map(F,J8))
    for i in range(8):p[i]-=v*J7[i]
    q=[F(0)]*8
    for i in range(7,-1,-1):q[i]=p[i+1];p[i]+=e*q[i]
    assert p[0]==0 and q[-1]>0
    for k in range(7):assert sum(a*(F(1,k+j+3)-e*F(1,k+j+2)) for j,a in enumerate(q))==0
    high=F(0); out=[]
    for i,b in enumerate(B.split(','),1):
        l,r=map(F,b.split())
        assert high<l<r<1 and (-1)**(7-i)*ev(q,l)<0<(-1)**(7-i)*ev(q,r)
        high=r;out.append((l,r))
    return out
plus=ref('1.13','.0519 .0520,.1673 .1674,.3301 .3302,.5180 .5181,.7053 .7054,.8652 .8653,.9716 .9717')
minus=ref('-.13','.0685 .0686,.2053 .2054,.3824 .3825,.5735 .5736,.7520 .7521,.8937 .8938,.9792 .9793')
S0=tuple(map(F,'.050 .161 .318 .5 .68155 .838 .949'.split()))
S1=tuple(map(F,'.020 .103 .240 .414 .600 .773 .911'.split()))
assert (3*F('.978')-S0[4])/2<F('1.13')
assert (3*F('.944')-S1[4])/2<F('1.13')
S0u=tuple(v for _,v in plus)
S1u=tuple(1-v for v,_ in reversed(minus))
def G(V,u,s):
    V,u,s=map(F,(V,u,s))
    m=lambda k:(V+u)/F(k+3)-V*u/F(k+2)-1/F(k+4)
    return tuple(m(k+1)-s*m(k) for k in range(3))
for lower,upper,cases in [
 (S0,S0u,[
  (2,6,5,'.186','.2','1.096','1.16','.842','.39','6191117/4375000000000'),
  (1,6,3,'.057','.063','1.096','1.16','.395',None,'2103912954179/630000000000000000'),
  (1,5,4,'.07','.077','1.345','1.426','.761','.25','405793501/134400000000'),
 ]),
 (S1,S1u,[
  (2,6,5,'.129','.138','1.146','1.206','.8','.25','76739/210000000'),
  (1,6,3,'.025','.027','1.146','1.206','.321',None,'3728361493119367/126000000000000000000'),
  (1,5,4,'.032','.035','1.475','1.553','.711','.25','38259839/5376000000'),
 ]),
]:
    for first,a,contr,ul,uh,vl,vh,s,r,answer in cases:
        first,a,contr=first-1,a-1,contr-1
        ul,uh,vl,vh,s=map(F,(ul,uh,vl,vh,s))
        assert lower[first]/upper[a]>=ul and upper[first]/lower[a]<=uh
        assert lower[6]/upper[a]>=vl and upper[6]/lower[a]<=vh
        assert upper[contr]/lower[a]<s
        GS=[G(v,u,s) for v in (vl,vh) for u in (ul,uh)]
        if r is None:
            assert min(x for x,_,_ in GS)>0
            vals=[x*z-y*y for x,y,z in GS]
        else:
            r=F(r);vals=[x*r*r-2*y*r+z for x,y,z in GS]
        assert min(vals)==F(answer)>0
print('Exact exterior-secondary references, root-rank bounds, and six Gram boxes verified.')

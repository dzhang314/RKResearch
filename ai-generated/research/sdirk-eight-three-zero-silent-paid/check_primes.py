#!/usr/bin/env python3
from gauss import ctx,phase
from itertools import permutations
found=[]
for p in (13,19,137):
 F,R,dd,rs=ctx(p)
 print('prime',p,dd)
 for a,b in permutations(rs,2):
    k=a+b-2;q=(a+b)*k-a*b+9*F.one()/7
    r=lambda x:x*x+k*x+q
    j=lambda x:x*x*x/3+k*x*x/2+q*x
    jx=lambda x:x**4/4+k*x**3/3+q*x*x/2
    g=(j(F.one())-j(b))/r(b)
    if not g or r(g)==0 or r(1-g)==0:continue
    D=j(a)-g*r(a);N=jx(a)-g*a*r(a)
    if D==0:
        if N!=0:continue
        s=None
    else:
        s=N/D
        if s in (a,b) or r(s)==0 or j(s)!=g*r(s):continue
    def end(k,R,y,z,eps):
        ds=R+g*g;ns=2*R-g*(2*g+k)
        if ds==0:
            assert ns!=0,('free gap',a,b,g,R,k)
            return []
        u=ns/ds;output=[]
        for kind,w,kg,t in phase(u):
            c=y(g*(1+w))
            if kg!=0 and R*kg==r(c):output.append((kind,u,c,kg,t))
            if kg==0 and kind=='A':
                if z is None and r(c)!=0 and g*r(c)==j(c) and c not in (a,b):
                    output.append(('Z',u,c,kg,t))
                if c==z:output.append(('Z',u,c,kg,t))
        return output
    fs=end(k,r(g),lambda y:y,s,1)
    rr=end(-2-k,r(1-g),lambda y:1-y,b,-1)
    print('anchors',a,b,g,s,'front',fs,'rear',rr)
    assert not rr
    found.append((p,int(a),int(b),int(g),s))
assert found==[(19,3,17,4,None),(137,40,98,117,None)]

from probe import *
from math import lcm
def tests(x):
    s=2*x-1;d=x*(1-x)
    return d*(5*s*s-1),d*s*(7*s*s-3)
def eg(a,b):
    if not b:
        return abs(a),(-1 if a<0 else 1),0
    g,k,l=eg(b,a%b)
    return g,l,k-(a//b)*l

def obs(d,q,early,last,s=F(1),t=F(0)):
    assert set(early+last)==set(nodes)-{d}
    assert q not in early and q in last
    c=[F(1),*early,*last,q,d,F(1)]
    w=[F(1),*(s if x==q else C[x]for x in (*early,*last)),C[q]-s,C[d],C[F(1)]-1]
    n=-C[early[0]]*(1-early[0])**2/(2*b[early[0]])
    u=[F(0),*(t if x==q else n*b[x]for x in (*early,*last)),n*b[q]-t,n*b[d],F(0)]
    return c,w,u

def good():
    for d,q in permutations(nodes,2):
        dm=det(list(zip(tests(d),tests(q))))
        if not unit(dm):continue
        rest=tuple(x for x in nodes if x not in (q,d))
        for early in permutations(rest,3):
            if not unit(C[early[0]]): continue
            last=tuple(x for x in (*rest,q) if x not in early)
            c,w,u=obs(d,q,early,last)
            a,b,c0=assess(c,w,u)
            if not (unit(a) and unit(b)): continue
            c,w,u=obs(d,q,early,last,t=F(1))
            c1=assess(c,w,u)[2]-c0
            D=lcm(c0.denominator,c1.denominator)
            A,B=(int(z*D)for z in (c0,c1))
            g,s,t=eg(A,B)
            if unpaid(g)!=1:continue
            # use small cofactor split, chosen to make determinant's numerator a paid unit.
            if unit(c1):
                for dt in (F(1,1000),-F(1,1000), F(1,10**9),-F(1,10**9)):
                    ts=(dt-c0)/c1
                    if paid(ts):
                        yield d,q,early,last,F(1),ts,(a,b,dt),dm
            else:
                for k in (0,1,-1,2,-2):
                    ss=s+k*(B//g); ts=t-k*(A//g)
                    if ss and ss!=C[q]:
                        yield d,q,early,last,F(ss),F(ts),(a,b,F(g,D)),dm
if __name__=='__main__':
    from sys import exit
    count=0
    for z in good():
        count+=1
        print(z,flush=True)
    print('count',count)

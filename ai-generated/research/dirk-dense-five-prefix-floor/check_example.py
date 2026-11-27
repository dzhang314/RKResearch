"""Seven actual lower triangular stages with an honest size-five decoder."""
from fractions import Fraction as Q
from math import factorial, lcm

def mul(a,b):
    w=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            w[i+j]+=x*y
    return w
def evaluate(f,v):
    return sum(t*v**k for k,t in enumerate(f))
def cardinal(nodes):
    out=[]
    for u in nodes:
        w=[Q(1)]
        for v in nodes:
            if u!=v:w=mul(w,[-v/(u-v),1/(u-v)])
        out.append(w)
    return out
def integrate(f,v):
    return sum(t*v**k/k for k,t in enumerate(f,1))

c=list(map(Q,("0","1/4","1/2","1","3/2","2","5/2")))
sets=[(0,),(0,1),(0,1,2),(0,2,3),(0,2,3,4),(0,2,3,5),(0,2,3,6)]
A=[[Q(0)]*(i+1) for i in range(7)]
for i,js in enumerate(sets):
    for j,f in zip(js,cardinal([c[k]for k in js])):
        A[i][j]=integrate(f,c[i])
assert list(map(sum,A))==c
read=[0,3,4,5,6]
Pi=cardinal([c[i] for i in read])
D=lcm(*(x.denominator for row in A+Pi for x in row))
assert factorial(5)**2 % D == 0

def apply(v):
    return tuple(sum(x*y for x,y in zip(r,v))for r in A)
past=[]
counts=[]
for n in range(1,6):
    layer=[]
    def gen(left,j,v,fac):
        if not left:
            for k in range(5):
                want=Q(n,fac) if k==n-1 else Q(0)
                assert sum(f[k]*v[i] for i,f in zip(read,Pi))==want
            layer.append((n,fac,apply(v)))
            return
        for t in range(j,len(past)):
            m,f,w=past[t]
            if m>left:break
            gen(left-m,t,tuple(x*y for x,y in zip(v,w)),fac*f)
    gen(n-1,0,(Q(1),)*7,n)
    past.extend(layer);counts.append(len(layer))
assert counts==[1,1,2,4,9]
print("seven-stage honest degree-four decoder; all 17 true rooted cases",counts)
print("literal matrix and decoder common denominator",D,"divides (5!)^2")
for i,r in enumerate(A): print("row",i+1,*(str(v) for v in r))

#!/usr/bin/env python3
"""Complete quartic characteristic classifier. Python stdlib only.
Independent full grid and Hadamard/CRT certificate for the joint M,B norm.
Each listed composite component gets two exact monic polynomial gcd proofs:
verified Bezout identities *and* both divisibilities, so they remain valid
over every residue prime, even without factoring the integer component.
All units are tested by explicit inverse and multiplication; therefore
nonzero pivot and amplitude tests are preserved after reduction.
"""
from pathlib import Path
from math import gcd,isqrt
import sys,json
sys.path.insert(0,sys.argv[1])
from verify_indices import fieldres
from check_pencil_projection import trim,ev,res,F,J
class S:
 def __init__(self,m,g=(0,1)):self.m,self.g=m,g;assert len(g) in (2,3) and g[-1]==1;self.d=len(g)-1
 def cn(self,x):return (x%self.m,0)
 def plus(self,u,v):return ((u[0]+v[0])%self.m,(u[1]+v[1])%self.m)
 def neg(self,u):return ((-u[0])%self.m,(-u[1])%self.m)
 def mul(self,u,v):
    m=self.m;a,b=u;c,d=v
    if self.d==1:assert not b and not d;return self.cn(a*c)
    c0,c1,_=self.g
    return ((a*c-c0*b*d)%m,(a*d+b*c-c1*b*d)%m)
 def inv(self,u):
    m=self.m;a,b=u
    if self.d==1:v=self.cn(pow(a,-1,m))
    else:
       c0,c1,_=self.g;adj=((a-c1*b)%m,-b%m);norm=self.mul(u,adj);assert not norm[1]
       v=self.mul(adj,self.cn(pow(norm[0],-1,m)))
    assert self.mul(u,v)==self.cn(1);return v
 def unit(self,u):
    if u==self.cn(0):return False
    self.inv(u);return True
 def normpoly(self,x):
    x=list(x)
    while x and x[-1]==self.cn(0):x.pop()
    return x
 def add(self,a,b):
    return self.normpoly([self.plus((a[i] if i<len(a) else self.cn(0)),(b[i] if i<len(b) else self.cn(0))) for i in range(max(len(a),len(b)))])
 def sc(self,a,k):return self.normpoly([self.mul(v,k) for v in a])
 def prod(self,a,b):
    r=[self.cn(0)]*max(0,len(a)+len(b)-1)
    for i,x in enumerate(a):
       for j,y in enumerate(b):r[i+j]=self.plus(r[i+j],self.mul(x,y))
    return self.normpoly(r)
 def div(self,a,b):
    r=self.normpoly(a);b=self.normpoly(b);q=[self.cn(0)]*max(0,len(r)-len(b)+1);v=self.inv(b[-1])
    while len(r)>=len(b):
       j=len(r)-len(b);x=self.mul(r[-1],v);q[j]=x
       for k in range(len(b)):r[j+k]=self.plus(r[j+k],self.neg(self.mul(x,b[k])))
       r=self.normpoly(r)
    q=self.normpoly(q);assert self.add(self.prod(b,q),r)==self.normpoly(a)
    return q,r
 def gcd(self,f,g):
    f=self.normpoly(f);g=self.normpoly(g);a=f;b=g;s=[self.cn(1)];t=[];u=[];v=s
    while b:
       q,r=self.div(a,b);a,b=b,r
       s,t=t,self.add(s,self.sc(self.prod(q,t),self.cn(-1)))
       u,v=v,self.add(u,self.sc(self.prod(q,v),self.cn(-1)))
    w=self.inv(a[-1]);D=self.sc(a,w);s=self.sc(s,w);u=self.sc(u,w)
    # These three independent identities prove the gcd over every field reduction;
    # unlike testing just that the recorded arrays have the expected true length.
    assert self.add(self.prod(s,f),self.prod(u,g))==D and D[-1]==self.cn(1)
    assert not self.div(f,D)[1] and not self.div(g,D)[1]
    return D
 def val(self,f,x):
    v=self.cn(0)
    for a in reversed(f):v=self.plus(self.mul(v,x),a)
    return v
 def ints(self,f):return self.normpoly([self.cn(x) for x in f])
def main(src,base):
 D=next(d for d in json.loads((src/'integer_ports.json').read_text()) if d['name']=='quartic')
 ext=json.loads((base/'exact_quartic_outer.json').read_text());R,T=ext['R'],ext['T']
 orig=abs(int(json.loads((base/'index_quartic.json').read_text())['raw_hex'],16))
 d=json.loads((base/'quartic_mixed_0.json').read_text());U=d['U'];I=int(d['norm'],16)
 for z in range(161):
    a=[ev(c,z) for c in D['C']];b=[ev(c,z) for c in D['H'][0]]
    assert res(a,b,10,14)==ev(U,z)
 B=sum(x*x for x in R)**(len(U)-1)*sum(x*x for x in U)**(len(R)-1)
 assert I and I*I<=B
 lim=1000000;ss=bytearray(b'\1')*(lim+1);ss[:2]=b'\0\0'
 for i in range(2,isqrt(lim)+1):
    if ss[i]:ss[i*i::i]=b'\0'*((lim-i*i)//i+1)
 P=1;k=0
 for p in range(lim,1,-1):
    if not ss[p]:continue
    assert fieldres(R,U,p)==I%p;k+=1;P*=p
    if P*P>4*B:break
 assert P*P>4*B
 print('Joint integer U degree',len(U)-1,'161 verified Bareiss samples;',abs(I).bit_length(),'index bits and',k,'prime residues within the proved CRT bound.',flush=True)
 N=gcd(abs(I),orig)
 small=[]
 for p in [2,3,5,7,11,13]:
    e=0
    while not N%p:N//=p;e+=1
    small.append(e)
 print('small gcd valuations',small,'non-small support bits',N.bit_length())
 comps=[43,53,109,107451025593855819651531329774816424560049512380020377454517620130829,
        7109270134834058998139,104295260060968696963648183,2551619843329,65637022433]
 prod=1;left=N
 for m in comps:
    assert not N%m and gcd(prod,m)==1;prod*=m
    while gcd(left,m)>1:left//=gcd(left,m)
 assert left==1
 accepted=[];rec=[]
 for m in comps:
    V=S(m);g=V.gcd(V.ints(R),V.ints(T));g=[x[0] for x in g];assert len(g) in (2,3)
    L=S(m,g);z=L.cn(-g[0]) if len(g)==2 else (0,1)
    assert L.val(L.ints(g),z)==L.cn(0)
    if len(g)==3:assert gcd((g[1]**2-4*g[0]),m)==1
    A,M,B=([L.val(L.ints(row),z) for row in P] for P in [D['A'],D['C'],D['H'][0]])
    d=L.gcd(A,M);assert len(d)==2;t=L.neg(d[0]);u=L.mul(z,t)
    assert L.val(A,t)==L.val(M,t)==L.cn(0)
    if not L.unit(z) or not L.unit(L.plus(z,L.cn(-1))) or not L.unit(t):
        print(m,'reject: t, z or z-1 zero');continue
    if L.unit(L.val(B,t)):
        print(m,'reject: B unit');continue
    f=L.val(L.ints(F),t);j=L.val(L.ints(J),t)
    if not L.unit(f) or not L.unit(j):print(m,'reject: singular pencil');continue
    b=L.neg(L.mul(j,L.inv(f)));W=L.add(L.ints(J),L.sc(L.ints(F),b))
    if not L.unit(L.plus(b,L.cn(1))) or not L.unit(W[0]):print(m,'reject: terminal/origin guard');continue
    Q=[L.mul(t,u),L.neg(L.plus(t,u)),L.cn(1)];quart,rem=L.div(W,Q);assert not rem and len(quart)==5 and L.unit(quart[-1])
    if not L.unit(L.val(quart,t)) or not L.unit(L.val(quart,u)):print(m,'reject: pivot amplitude zero');continue
    def mom(k,y):return L.val([L.cn(0)]*(k+1)+[L.mul(v,L.inv(L.cn(k+i+1))) for i,v in enumerate(quart)],y)
    cap=L.mul(mom(2,t),L.inv(L.mul(t,j)));assert mom(1,t)==L.cn(0)
    assert L.plus(mom(2,u),L.neg(L.mul(t,mom(1,u))))==L.mul(cap,L.mul(u,L.val(L.ints(J),u)))
    print(m,'accept: source gcd degree',len(g)-1,'; full literal normalized witness verified')
    accepted.append(m);rec.append({'m':m,'g':g,'t':t,'u':u,'b':b,'kappa':cap,'R':quart})
 E=1
 for m in accepted:E*=m
 assert E==40743825584966961425950943209234954914929956692140434167752418813578190817982950589
 (base/'quartic_global_accepted.json').write_text(json.dumps(rec,separators=(',',':'))+'\n')
 print('Global physical scalar exception iff p divides',E,flush=True)
if __name__=='__main__':main(Path(sys.argv[1]),Path(sys.argv[2]))

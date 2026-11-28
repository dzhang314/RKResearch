#!/usr/bin/env python3
"""Univariate reconstruction over p^k; no search or floating point."""
import argparse,json
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
HERE=Path(__file__).resolve().parent
def load(n,p):
    z=spec_from_file_location(n,p);v=module_from_spec(z);z.loader.exec_module(v);return v
g=load('full_geometry',HERE.parent/'erk10-fifteen-17-power'/'geometry.py')
NONIC=[5376000,-10590720,9105600,-4477616,1385568,-279450,36720,-3036,144,-3]
GRAM=[896,-840,300,-48,3]
MN=[5600,-5400,1984,-327,21]
NN=[1600,-1600,611,-105,7]

def ev(f,a,m):
    v=0
    for x in f:v=(v*a+x)%m
    return v

def derivative(f):return [a*(len(f)-1-i)for i,a in enumerate(f[:-1])]

def tail(a,mod):
    inv=pow(5*ev(GRAM,a,mod),-1,mod)
    return -ev(MN,a,mod)*inv%mod,ev(NN,a,mod)*inv%mod

def coords(a,d,f,mod):
    assert ev(NONIC,a,mod)==0
    m,n=tail(a,mod)
    assert (f*f+m*f+n)%mod==0
    z=(-m-f)%mod
    b=2*a%mod
    U=g.poly([1,f,z])
    M=g.poly([0,0,b,b])
    UM=g.mul(U,M)
    s=[g.integ([0]*k+UM,mod)for k in range(3)]
    e=s[1]*pow(s[0],-1,mod)%mod
    assert (s[2]-e*s[1])%mod==0
    nu=g.poly([1,e,f,z])
    G1=g.poly([0,a,b])
    F=g.mul(g.mul(nu,[-d,1]),G1)
    c=g.integ([0]+F,mod)*pow(g.integ(F,mod),-1,mod)%mod
    out=[a,c,d,e,f,z]
    assert g.system(out,mod)==[0]*5
    return out

def series(prime,a,d,f,maxexp):
    a%=prime;f%=prime
    m,n=tail(a,prime)
    sigma=ev(derivative(NONIC),a,prime)
    tau=(2*f+m)%prime
    sinv=pow(sigma,-1,prime)
    tinv=pow(tau,-1,prime)
    assert ev(NONIC,a,prime)==0 and (f*f+m*f+n)%prime==0
    y={}
    p=prime
    for k in range(1,maxexp+1):
        y[k]=coords(a,d%p,f,p)
        if k==maxexp:break
        pp=p*prime
        va=ev(NONIC,a,pp)
        assert va%p==0
        a+=p*(-(va//p)*sinv%prime)
        m,n=tail(a,pp)
        vf=(f*f+m*f+n)%pp
        assert vf%p==0
        f+=p*(-(vf//p)*tinv%prime)
        p=pp
    return y
if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--prime',type=int,default=17)
    p.add_argument('--a',type=int,default=16)
    p.add_argument('--d',type=int,default=8)
    p.add_argument('--f',type=int,default=4)
    p.add_argument('--maxexp',type=int,default=9)
    z=p.parse_args()
    ob=series(z.prime,z.a,z.d,z.f,z.maxexp)
    print(json.dumps(ob,indent=2))
    if (z.prime,z.a,z.d,z.f,z.maxexp)==(17,16,8,4,9):
        old=json.loads((HERE.parent/'erk10-fifteen-17-power'/'geometry-lifts.json').read_text())
        assert {str(k):v for k,v in ob.items()}==old

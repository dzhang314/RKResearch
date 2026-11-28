"""Exact common-fibre arithmetic for the distinct one-extra label envelope."""
from distinct_d_extra_other import *
def main():
    out=[]
    for patt,kind,f,r,fs,ans in cases():
        if not fs:continue
        assert len(fs)==1 and patt=='match' and kind=='split' and f==r
        pol,ex=fs[0];assert ex==1
        f0=S.Poly.from_dict({(int(i),):int(c) for (i,j),c in pol.to_dict().items()},X,domain=S.QQ)
        assert f0.is_irreducible
        K=S.QQ.algebraic_field((f0,X));hh=K.unit
        m=1+hh
        de=35*hh*hh-21*m*m
        assert de
        s=(21*m*m*hh*hh-15*m**4)/de
        (p,q),*_=ans
        mq=max(max(z.degrees()[0] for z in (p,q)),1)
        sq=max(max(z.degrees()[1] for z in (p,q)),1)
        hp=[hh**i for i in range(int(mq)+1)]
        sp=[s**j for j in range(int(sq)//2+1)]
        def red(z):
            f=[K.zero,K.zero]
            for (i,j),a in z.to_dict().items():
                f[int(j)%2]+=hp[int(i)]*sp[int(j)//2]*K.convert(int(a))
            return f
        a,b=red(p);c,d=red(q)
        det=a*d-b*c
        print('exact simultaneous d fibre',f,f0.degree(),'det nonzero?',bool(det),flush=True)
        assert det
        out.append((f,f0.degree()))
    assert out==[('A2',58),('A3',58),('S',32)]
    print('all nonmutual distinct one-extra-D cases excluded')
if __name__=='__main__':main()

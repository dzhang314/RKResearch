"""Exact scalar arithmetic for the physical clean-four graph and fifth-clock gate."""
from sympy import Poly, QQ, Rational, sqrt, symbols

x, r = symbols("X r")
L = [1, 2*x-1, 6*x**2-6*x+1, 20*x**3-30*x**2+12*x-1,
     70*x**4-140*x**3+90*x**2-20*x+1]


def integral(f):
    return sum(v * r**j / (i+1) for (i, j), v in Poly(f,x,r,domain=QQ).terms())


def moment_kernel():
    K = sum((2*j+1)*L[j]*Poly(L[j],x).eval(r) for j in range(4))
    for j in range(4):
        assert integral(x**j*K) == r**j
        assert integral(x**j*L[4]) == 0
    assert integral(L[4]**2) == Rational(1,9)


Y,S,G = symbols("y s gamma")
t=sqrt(2)/2
K=QQ.algebraic_field(t)


def P(f):
    return Poly(f,Y,S,G,domain=K)


def scalar(f):
    return K.to_sympy(K.convert(f))


def coefficient(f,n):
    return Poly.from_dict({(0,j,k):v for (i,j,k),v in f.rep.to_dict().items()
                          if i==n}, (Y,S,G), domain=K)


def exact(a,b):
    q,rem=a.div(b)
    assert rem.is_zero
    return q


def substitute_y(f,a):
    # Reinstate the three-variable ring after anchored substitution.
    return P(f.eval(Y,a).as_expr())


def literal_graph(star):
    aa=scalar(2+2*t)
    bb=scalar(2-2*t if star else 3+4*t)
    m=scalar(0 if star else (1+6*t)/2)
    ha=scalar((aa-1)/2)
    hb=scalar((bb-1-m)/2)
    assert scalar(aa-bb) != 0
    assert ha and hb
    A,B,M,HA,HB=map(P,(aa,bb,m,ha,hb))
    u,s,g=map(P,(Y,S,G))
    tau_a=A**3+A-1-A**4*Rational(1,4)
    tau_b=B**3+B-1-M+M*A**3-B**4*Rational(1,4)

    def line(va,vb,v):
        return exact(exact(va*(B-v),HA)+exact(vb*(v-A),HB),B-A)

    def L4(v):
        return 1-20*g*v+90*(g*v)**2-140*(g*v)**3+70*(g*v)**4

    def moments(v,h):
        return v-1-2*h, v**2*Rational(1,2)-v-2*h, v**3*Rational(1,3)-v**2-Rational(4,3)*h

    m0,m1,m2=moments(u,P(0))
    den=P(-Rational(4,3))+2*(A+B)-2*A*B
    assert den != P(0)
    h4=exact(-(m2-(A+B)*m1+A*B*m0),den)
    hh=P(h4.as_expr().subs(Y,S))
    assert substitute_y(h4,aa)==HA and substitute_y(h4,bb)==HB
    v0,v1,v2=moments(u,h4)
    assert v2-(A+B)*v1+A*B*v0==P(0)
    tap_a=exact(B*v0-v1,B-A)
    tap_b=v0-tap_a
    Ah=h4+tap_a*HA+tap_b*HB
    Th=u**3-u**4*Rational(1,4)+2*h4+tap_a*A**3+tap_b*B**3
    L_a,L_b=L4(A),L4(B)
    ellL,ellA,ellT=[line(a,b,u) for a,b in ((L_a,L_b),(HA,HB+M*HA),(tau_a,tau_b))]
    pad2=(u-A)*(u-B)
    rv=exact(Ah-ellA*h4,pad2)
    rt=exact(Th-ellT*h4,pad2)
    dq=exact(L4(u)-ellL*h4,pad2)
    if star:
        assert rv==rt==P(Rational(1,4))
        assert h4==P(Rational(3,4))-Rational(9,4)*u+Rational(9,8)*u**2-Rational(1,8)*u**3
    else:
        assert rv==P(-Rational(197,14)+Rational(138,7)*t)+P(-55+78*t)*u+P(Rational(243,14)-Rational(172,7)*t)*u**2
        assert rt==P(-Rational(4,7)-Rational(9,7)*t)+P(Rational(1,2)+3*t)*u+P(Rational(3,28)-Rational(4,7)*t)*u**2
        assert h4==P(-3+3*t)+P(Rational(45,2)-30*t)*u+P(-Rational(141,4)+Rational(99,2)*t)*u**2+P(Rational(17,2)-12*t)*u**3
    assert rv.gcd(rt)==P(1)
    assert dq.degree(Y)<=2
    rv,rt,dq=[P(f.as_expr().subs(Y,S)) for f in (rv,rt,dq)]

    # Exact polynomials of degree at most two matching the three actual
    # nonfirst predecessor data. Their functional read uses moments M0..M2.
    pad3=pad2*(u-s)
    h_interp=h4-coefficient(h4,3)*pad3
    c3_interp=u**3-pad3
    for a,actual in ((aa,HA),(bb,HB)):
        assert substitute_y(h_interp,a)==actual
    assert P(h_interp.as_expr().subs(Y,S))==hh

    def literal_diffs(h):
        moments3=moments(u,h)
        read=lambda f: sum((coefficient(f,i)*m0 for i,m0 in enumerate(moments3)),P(0))
        return h+read(h_interp)-ellA*h, u**3-u**4*Rational(1,4)+2*h+read(c3_interp)-ellT*h, L4(u)-ellL*h

    a0,b0,l0=literal_diffs(P(0))
    a1,b1,l1=[v1-v0 for v1,v0 in zip(literal_diffs(P(1)),(a0,b0,l0))]
    eq_a0,eq_a1=dq*a0-rv*l0,dq*a1-rv*l1
    eq_b0,eq_b1=dq*b0-rt*l0,dq*b1-rt*l1
    determinant=eq_a0*eq_b1-eq_a1*eq_b0
    for node,amp in ((A,HA),(B,HB),(s,hh)):
        # Actual earlier stages pad the literal equations, not just a sampled
        # specialisation. Their predecessor sets are included by zero taps.
        for f0,f1 in ((eq_a0,eq_a1),(eq_b0,eq_b1)):
            assert P((f0+amp*f1).as_expr().subs(Y,node.as_expr()))==P(0)
    q5=exact(exact(determinant,dq),pad3)
    assert not q5.is_zero and q5.degree(Y)<=2
    q0,q1,q2=[coefficient(q5,i).as_expr() for i in range(3)]
    dogs=[(coefficient(q5,i).degree(S),coefficient(q5,i).degree(G))
          for i in range(3)]
    gamma=lambda p:Poly(p,G,domain=K)
    slope=rt*a1-rv*b1
    offset=exact(rt*a0-rv*b0+slope*h4,pad3)
    if star:
        assert dogs==[(2,4),(1,4),(0,4)]
        e=(3*s-1)*Rational(1,2)
        assert slope==(u-e)*Rational(1,2) and offset==P(0)
        dy=P(dq.as_expr().subs(S,Y))
        assert q5==exact(dy-dq,u-s)*(u-e)*Rational(1,2)
        assert P(q1.coeff(S,1))==-P(q2)*Rational(1,2)
        assert gamma(q2).gcd(gamma(q1.coeff(S,0)))==gamma(1)
        assert gamma(dq.as_expr().coeff(S,2)).gcd(
               gamma(dq.as_expr().coeff(S,1)))==gamma(1)
        # Actual clean sixth: this additional closed form is conditional
        # on the actual fifth amplitude being the literal cubic H4(y5).
        for h in (P(0),P(1)):
            w0,w1,w2=moments(u,h)
            AHd=dq*ellA*h+rv*(L4(u)-ellL*h)
            THd=dq*ellT*h+rt*(L4(u)-ellL*h)
            w3d=dq*(u**4*Rational(1,4)-u**3-2*h)+THd
            gate=AHd-dq*(h+Rational(3,4)*w0-Rational(9,4)*w1
                             +Rational(9,8)*w2)+Rational(1,8)*w3d
            assert 32*gate==9*(L4(u)-ellL*h)+dq*(
                u**4-16*u**3+72*u**2-96*u+24+(4*ellT-56)*h)
    else:
        assert dogs==[(2,4),(2,4),(1,4)]
        kappa=Rational(729,56)-Rational(129,7)*t
        assert scalar(kappa)!=0
        assert offset==P(kappa)*(s+u-6-P(4*t))
        a,b=[gamma(q2.coeff(S,i)) for i in (1,0)]
        assert a.gcd(b)==gamma(1)
        def homogeneous_root_value(C):
            pp=Poly(C,S)
            assert pp.degree()==2
            return sum((gamma(pp.nth(i))*(-b)**i*a**(2-i) for i in range(3)),
                       gamma(0))
        c,d=map(homogeneous_root_value,(q0,q1))
        assert c.degree()==d.degree()==12 and c.gcd(d)==gamma(1)
        theta=lambda p:Poly(p,S,domain=K)
        aa,bb=[theta(coefficient(slope,i).as_expr()) for i in (1,0)]
        assert (aa.degree(),bb.degree())==(2,3) and aa.gcd(bb)==theta(1)
        U=theta(S-2+2*t)
        V=theta(S**2+(-6-8*t)*S+Rational(237,17)+Rational(380,17)*t)
        assert theta(slope.as_expr().subs(Y,6+4*t-S))==theta(
            Rational(3,14)-Rational(8,7)*t)*U*V
    print("star" if star else "arithmetic", "front: fourth readings coprime;",
          "fifth coefficient degrees",dogs,"; no identically zero fiber;",
          "exact combined fifth slope and exceptional branch",flush=True)
    return q5,(dq,rv,rt,ellL,ellA,ellT,(a0,a1),(b0,b1),(l0,l1),
               (eq_a0,eq_a1),(eq_b0,eq_b1))


def row6_clean_interpolation():
    # Fully polynomial audit of the denominator-free quartic shortcut:
    # H - leading(H)*E4 has degree <=3 and agrees at all four predecessors.
    nodes=symbols("a b q y5")
    cc=symbols("h0:5")
    ring=(x,*nodes,*cc)
    E=Poly(1,*ring,domain=QQ)
    for w in nodes:
        E*=Poly(x-w,*ring,domain=QQ)
    H=Poly(sum(cc[i]*x**i for i in range(5)),*ring,domain=QQ)
    P3=H-Poly(cc[4],*ring,domain=QQ)*E
    assert P3.degree(x)==3
    for w in nodes:
        assert Poly((H-P3).as_expr().subs(x,w),*ring,domain=QQ).is_zero


if __name__=="__main__":
    moment_kernel()
    for star in (True,False):
        literal_graph(star)
    row6_clean_interpolation()
    print("verified: reproducing kernel, literal fourth, both Q5 branches, row-six quartic interpolation")

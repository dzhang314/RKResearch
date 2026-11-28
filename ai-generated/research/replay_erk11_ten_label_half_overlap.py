"""Independent integer replay of the two half-overlap minors and Bezout."""
R4 = (1, -14, 56, -84, 42)
R5 = (-1, 20, -120, 300, -330, 132)

def clean(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:a.pop()
    return tuple(a)

def mul(a,b):
    p=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):p[i+j]+=u*v
    return clean(p)

def add(a,b):
    p=[0]*max(len(a),len(b))
    for i,u in enumerate(a):p[i]+=u
    for i,v in enumerate(b):p[i]+=v
    return clean(p)

def scale(a,c):
    return clean(c*u for u in a)

def sub(a,b):
    return add(a,scale(b,-1))

def comp(a,b):
    p=(0,)
    for u in reversed(a):p=add(mul(p,b),(u,))
    return p

def deriv(a):
    return tuple(i*u for i,u in enumerate(a) if i)

x1=(-1,1)
j=(353,-5648,31864,-89520,142332,-134064,74088,-22176,2772)
ell=(325,-5086,27269,-70968,102015,-85050,41202,-11088,1386)
u=(16195538392,-231428849627,1051816146834,-2164681755495,
   2294810833140,-1306784001159,393390636408,-54796857192)
v=(-17590600202,257541514243,-1245912798462,2833482948828,
   -3434808706056,2284786859166,-786781272816,109593714384)
assert sub(mul(R4,comp(R5,x1)),mul(R5,comp(R4,x1)))==scale(j,-2)
assert sub(mul(R4,add(deriv(R5),comp(deriv(R5),x1))),
           mul(R5,add(deriv(R4),comp(deriv(R4),x1))))==scale(ell,8)
assert add(mul(u,j),mul(v,ell))==(79986726,)
print("Ten-label half-overlap minors and integer Bezout verified.")

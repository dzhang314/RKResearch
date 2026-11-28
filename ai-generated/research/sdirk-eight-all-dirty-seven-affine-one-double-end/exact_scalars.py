"""Small shared scalar polynomials, with no projection performed at import."""
def l3(y,d):return 5*y**3-3*d*d*y
def l4(y,d):return 35*y**4-30*d*d*y*y+3*d**4
def kk(y,z,d):
    return -9*d**6+15*d**4*y*y-75*d**4*y*z+15*d**4*z*z+105*d*d*y**3*z-45*d*d*y*y*z*z+105*d*d*y*z**3-175*y**3*z**3
def den(u):return 2*(u-2)*(u**3-3*u*u+1)
def hub(u):return -2+u+4*u*u-u**3
def kap(u):return 1+2*u-u*u
def num(u):return (1+4*u-4*u*u)*hub(u)+4*u*u*(3*u-2)

/* Optional FLINT 3.6 LP64 geometric-grid resultant. The coefficient
   powers at degree drops are part of the padded Sylvester determinant. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>

typedef unsigned long limb;
typedef long count;
typedef struct { limb n, inv, norm; } mod_t;
typedef struct { limb *c; count cap, len; mod_t mod; } poly;
typedef struct { _Alignas(16) limb opaque[256]; } geo;
extern void nmod_poly_init2(poly *, limb, count);
extern void nmod_poly_clear(poly *);
extern limb nmod_poly_get_coeff_ui(const poly *, count);
extern limb nmod_poly_resultant(const poly *, const poly *);
extern void _nmod_geometric_progression_init_function(geo *, limb, count, mod_t, limb);
extern void nmod_geometric_progression_clear(geo *);
extern void _nmod_poly_evaluate_geometric_nmod_vec_fast_precomp(limb *,
    const limb *, count, const geo *, count, mod_t);
extern void nmod_poly_interpolate_geometric_nmod_vec_fast_precomp(poly *,
    const limb *, const geo *, count);

static limb mul(limb a, limb b, limb p) {
    return (limb)(((__uint128_t)a*b)%p);
}
static limb power(limb a, count n, limb p) {
    limb z=1;
    while (n) {
        if (n&1) z=mul(z,a,p);
        a=mul(a,a,p); n>>=1;
    }
    return z;
}
static limb root_base(limb p,count n) {
    for (limb r=2;r<p && r<512;r++) {
        limb q=mul(r,r,p),a=1;
        count j;
        for (j=1;j<n;j++) {
            a=mul(a,q,p);
            if (a==1) break;
        }
        if (j==n) return r;
    }
    return 0;
}
static void fill(limb *out,const limb *a,count g,count s,count n,
                 geo *G,mod_t mod) {
    for (count j=0;j<=s;j++) {
        const limb *c=a+j*(g+1);
        count len=g+1;
        while (len>0 && !c[len-1]) len--;
        if (!len) {
            for (count i=0;i<n;i++) out[j*n+i]=0;
        } else {
            _nmod_poly_evaluate_geometric_nmod_vec_fast_precomp(
                    out+j*n,c,len,G,n,mod);
        }
    }
}
int interpolate_geometric(limb p,const limb *a,count g0,count s0,
                          const limb *b,count g1,count s1,
                          limb *out,limb mode) {
    if (sizeof(limb)!=8 || sizeof(count)!=8 || s0<1 || s1<1 ||
        g0<0 || g1<0) return -1;
    count cap=g0*s1+g1*s0, n=cap+1;
    if (n<=0 || (limb)n>p) return -2;
    limb r=root_base(p,n);
    if (!r) return -3;
    limb *v0=malloc((size_t)(s0+1)*n*sizeof(limb));
    limb *v1=malloc((size_t)(s1+1)*n*sizeof(limb));
    limb *yy=malloc((size_t)n*sizeof(limb));
    if (!v0 || !v1 || !yy) {free(v0);free(v1);free(yy);return -4;}
    poly P,Q,U;
    nmod_poly_init2(&P,p,s0+1);
    nmod_poly_init2(&Q,p,s1+1);
    nmod_poly_init2(&U,p,n);
    geo G;
    _nmod_geometric_progression_init_function(&G,r,n,P.mod,mode);
    fill(v0,a,g0,s0,n,&G,P.mod);
    fill(v1,b,g1,s1,n,&G,P.mod);
    count case0=0,case1=0,case2=0;
    for (count i=0;i<n;i++) {
        P.len=s0+1;Q.len=s1+1;
        for (count j=0;j<=s0;j++) P.c[j]=v0[j*n+i];
        for (count j=0;j<=s1;j++) Q.c[j]=v1[j*n+i];
        while (P.len>0 && !P.c[P.len-1]) P.len--;
        while (Q.len>0 && !Q.c[Q.len-1]) Q.len--;
        count dp=s0+1-P.len,dq=s1+1-Q.len;
        if (!P.len || !Q.len || (dp && dq)) {
            yy[i]=0;case0++;
        } else {
            limb z=nmod_poly_resultant(&P,&Q);
            if (dp) {
                if ((dp*s1)&1) z=z? p-z : z;
                z=mul(z,power(Q.c[s1],dp,p),p);
                case1++;
            }
            if (dq) {
                z=mul(z,power(P.c[s0],dq,p),p);
                case2++;
            }
            yy[i]=z;
        }
    }
    nmod_poly_interpolate_geometric_nmod_vec_fast_precomp(&U,yy,&G,n);
    for (count i=0;i<n;i++) out[i]=nmod_poly_get_coeff_ui(&U,i);
    nmod_geometric_progression_clear(&G);
    nmod_poly_clear(&P); nmod_poly_clear(&Q); nmod_poly_clear(&U);
    free(v0);free(v1);free(yy);
    return 0;
}

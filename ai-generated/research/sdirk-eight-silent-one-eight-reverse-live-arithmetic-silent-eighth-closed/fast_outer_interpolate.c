/* Exact resultant specialization at cap+1 full-degree points, LP64 FLINT. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>

/* Use opaque over-aligned storage; only the public FLINT methods read it. */
typedef struct { _Alignas(16) uint64_t opaque[64]; } poly;
typedef unsigned long limb;
typedef long count;
extern void nmod_poly_init(poly *, limb);
extern void nmod_poly_clear(poly *);
extern void nmod_poly_zero(poly *);
extern void nmod_poly_set_coeff_ui(poly *, count, limb);
extern limb nmod_poly_get_coeff_ui(const poly *, count);
extern void nmod_poly_evaluate_nmod_vec_fast(limb *, const poly *, const limb *, count);
extern void nmod_poly_interpolate_nmod_vec_fast(poly *, const limb *, const limb *, count);
extern limb nmod_poly_resultant(const poly *, const poly *);

static void evaluate_coefficients(limb p, const limb *input, count dg, count ds,
                                  const limb *pts, count num, limb *out) {
    poly a;
    nmod_poly_init(&a,p);
    for (count j=0; j<=ds; ++j) {
        nmod_poly_zero(&a);
        for (count k=0; k<=dg; ++k)
            nmod_poly_set_coeff_ui(&a,k,input[j*(dg+1)+k]);
        nmod_poly_evaluate_nmod_vec_fast(out+j*num,&a,pts,num);
    }
    nmod_poly_clear(&a);
}

int interpolate_outer(limb p, const limb *a, count g0, count s0,
                      const limb *b, count g1, count s1, limb *answer) {
    if (sizeof(limb)!=8 || sizeof(count)!=8 || g0<0 || g1<0 || s0<0 || s1<0)
         return -1;
    count cap=g0*s1+g1*s0, num=cap+1+g0+g1;
    if (num<=0 || (limb)num>p) return -2;
    limb *points=malloc((size_t)num*sizeof(limb));
    limb *v0=malloc((size_t)(s0+1)*num*sizeof(limb));
    limb *v1=malloc((size_t)(s1+1)*num*sizeof(limb));
    limb *xp=malloc((size_t)(cap+1)*sizeof(limb));
    limb *yp=malloc((size_t)(cap+1)*sizeof(limb));
    if (points==NULL || v0==NULL || v1==NULL || xp==NULL || yp==NULL) {
        free(points); free(v0); free(v1); free(xp); free(yp); return -3;
    }
    for (count i=0; i<num; ++i) points[i]=(limb)i;
    evaluate_coefficients(p,a,g0,s0,points,num,v0);
    evaluate_coefficients(p,b,g1,s1,points,num,v1);
    poly P,Q,U;
    nmod_poly_init(&P,p); nmod_poly_init(&Q,p); nmod_poly_init(&U,p);
    count at=0;
    for (count t=0; t<num && at<=cap; ++t) {
        /* At discarded sites the padded s-resultant need not agree
           with a resultant which first trims the univariate degrees. */
        if (!v0[s0*num+t] || !v1[s1*num+t]) continue;
        nmod_poly_zero(&P); nmod_poly_zero(&Q);
        for (count j=0; j<=s0; ++j) nmod_poly_set_coeff_ui(&P,j,v0[j*num+t]);
        for (count j=0; j<=s1; ++j) nmod_poly_set_coeff_ui(&Q,j,v1[j*num+t]);
        xp[at]=points[t]; yp[at]=nmod_poly_resultant(&P,&Q); ++at;
    }
    int rc=0;
    if (at<=cap) rc=-4;
    else {
        nmod_poly_interpolate_nmod_vec_fast(&U,xp,yp,cap+1);
        for (count j=0; j<=cap; ++j) answer[j]=nmod_poly_get_coeff_ui(&U,j);
    }
    nmod_poly_clear(&P); nmod_poly_clear(&Q); nmod_poly_clear(&U);
    free(points); free(v0); free(v1); free(xp); free(yp);
    return rc;
}

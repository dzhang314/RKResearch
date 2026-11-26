# Erratum: use the direct omitted-root primitive numerator

This corrects only the displayed “reduced moment numerator” and corresponding first Euclidean trace in `ORDER-TWELVE-CHAR283.md`. That note is otherwise unchanged. The branch conclusion and all later F283 data are unaffected.

Let D(x)=132x^5−330x^4+300x³−120x²+20x−1, let u be a root of D, and define P_u=D/(x−u) and I_u=J(xP_u)(u). Synthetic division gives
  60 I_u/u² = 600−6000u+19500u²−25410u³+11484u⁴.
For calculations over F283, the successive monic remainders for D and this exact numerator are [121,205,112,97,1], [215,241,231,1], and [190,282,1], in increasing coefficient order. The last is x²−x+190=(x−106)(x−178). These replace the different polynomial and its Euclidean trace in the earlier note. The direct coefficients and trace were independently checked by the uniform-audit worker.

For a transparent all-paid-field identification, put t=2u−1. Then
  80 I_u/u² =957t⁴−407t³−463t²+123t+22,
  D(u) = t(33t⁴−30t²+5)/8.
If t=0 the moment numerator is 22. Otherwise, for z=t² satisfying 33z²−30z+5=0, it reduces to (407z−123)(1−t). Here 1−t is nonzero since D(1)=1. The numeric combination 33·123²−30·123·407+5·407²=−2³·7·11·283 shows the simultaneous equations force characteristic 283 once 12! is a unit. In that characteristic 407z=123 gives z=90=72², hence u=106 or 178, even over extension fields. No shell process, solver, Lean, or repository action was used for this erratum.

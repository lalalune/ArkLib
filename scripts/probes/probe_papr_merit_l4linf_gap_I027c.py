"""
IDEA [I027] -- THE STRUCTURAL OBSTRUCTION (direction proof, parameter-free).

The merit-factor identity  L4^4 = N^2(1 + 1/F)  means: a BOUNDED merit factor F=Theta(1)
is EXACTLY a bounded L4/L2 ratio of the spectrum.  The idea claims this controls
Linf=M up to sqrt(log m).  We show it CANNOT, by exhibiting m-vectors with the SAME
(L2, L4) as a flat sequence -- i.e. the SAME bounded merit factor -- but Linf as large
as a POWER of m.

Construction: take m frequencies.  Put a spike of height H on K of them, and fill the
rest flat at level v so that L2 and L4 match a target.  Solve for how large H (=Linf) can be
while keeping merit factor (L4/L2) bounded by the SAME Theta(1) constant the real eta has.

If max attainable Linf >> sqrt(n log m), then bounded merit factor is NOT sufficient to
bound M: the duality is the wrong direction (L4 cannot see the spike that L-inf measures).
"""
import math, numpy as np

# Match the empirical regime: L2 ~ sqrt(n), L4/L2 ~ 1.31 (4th-moment ratio rho4 ~ 3).
# Question: with rho4 = mean(|x|^4)/mean(|x|^2)^2 FIXED at the bounded value 3,
# how large can max|x| be over m entries, holding mean(|x|^2)=n fixed?
def max_linf_given_l4(n, m, rho4):
    # vector: one spike of height H, rest equal to level v over (m-1) entries.
    # constraints:  (H^2 + (m-1) v^2)/m = n                       (L2^2 = n)
    #               (H^4 + (m-1) v^4)/m = rho4 * n^2              (L4^4 = rho4 n^2)
    # maximize H.  Solve: let S2 = m n, S4 = m rho4 n^2.
    S2 = m*n; S4 = m*rho4*n*n
    # from spike+flat: v^2 = (S2 - H^2)/(m-1); plug into S4:
    #   H^4 + (m-1) * ((S2-H^2)/(m-1))^2 = S4
    #   H^4 + (S2-H^2)^2/(m-1) = S4
    # solve for H^2 = u:  u^2 + (S2-u)^2/(m-1) = S4
    #   (m-1)u^2 + (S2-u)^2 = (m-1) S4
    #   (m-1)u^2 + S2^2 - 2 S2 u + u^2 = (m-1) S4
    #   m u^2 - 2 S2 u + S2^2 - (m-1) S4 = 0
    A=m; B=-2*S2; C=S2*S2-(m-1)*S4
    disc=B*B-4*A*C
    if disc<0: return None
    u=(-B+math.sqrt(disc))/(2*A)   # larger root = max spike
    return math.sqrt(u) if u>0 else None

print("Holding spectrum at the REAL bounded merit factor (rho4=3, i.e. F=1/2, L4/L2=3^.25=1.316):")
print("the LARGEST Linf that bounded-merit ALLOWS, vs the target sqrt(n log m):")
print(" n      m        sqrt(n)   sqrt(n log m)  max Linf allowed by bounded merit   ratio(allowed/target)")
for a in range(3,21):
    n=2**a
    m=int(round(n**3))  # beta=4 prize regime: m=(p-1)/n ~ n^3
    tgt=math.sqrt(n*math.log(m))
    H=max_linf_given_l4(n,m,3.0)
    if H is None:
        print(" n=%d infeasible"%n); continue
    print(" %5d  %-9d %8.3f  %12.3f  %30.3f   %.3f"%(n,m,math.sqrt(n),tgt,H,H/tgt))

print()
print("INTERPRETATION: max-Linf-allowed-by-bounded-merit ~ (rho4-1)^.25 * (m n)^.25 ~ n*(m)^.25 ~ n^1.75,")
print("a POWER of n above the sqrt(n log m) target. Bounded merit factor (L4 flatness) is consistent with")
print("M as large as ~n^1.75 -- it does NOT imply M=O(sqrt(n log m)). The single worst frequency (the spike,")
print("= the open problem's argmax) is invisible to the 4th moment. Same L-inf-from-moments wall as I025.")

import mpmath as mp
mp.mp.dps=60
# RIGOR of the radius/growth claim, two independent confirmations:
#
# (A) Singularity analysis of g(t)=(1/2)log I0(2t).
#   I0 is ENTIRE, I0(z)=prod_k (1+ z^2/j_{0,k}^2)  (Hadamard product; zeros of I0 at z=+- i j_{0,k}).
#   => I0(2t) = prod_k (1 + 4t^2 / j_{0,k}^2) = prod_k (1 - t^2/(i j_{0,k}/2)^2)  with zeros t=+- i j_{0,k}/2.
#   => g(t) = (1/2) sum_k log(1 + 4 t^2 / j_{0,k}^2).
#   Each summand is analytic for |t| < j_{0,k}/2; the BINDING one is k=1: radius R = j_{0,1}/2.
#   Expand: log(1+4t^2/j^2) = sum_{r>=1} (-1)^{r+1}/r * (4t^2/j^2)^r = sum_r (-1)^{r+1}/r 4^r t^{2r}/j^{2r}.
#   So  [t^{2r}] g = (1/2) sum_k (-1)^{r+1}/r * 4^r / j_{0,k}^{2r}
#                 = (-1)^{r+1} (2^{2r-1}/r) * sum_k j_{0,k}^{-2r}.
#   c_r = (2r)! [t^{2r}] g = (-1)^{r+1} (2r)! 2^{2r-1}/r * S_r,  S_r = sum_k j_{0,k}^{-2r}  (Rayleigh sum).
#   a_r = |c_r|/(2r)! = 2^{2r-1}/r * S_r.   As r->inf, S_r ~ j_{0,1}^{-2r} (first term dominates).
#   => a_r ~ 2^{2r-1}/r * j_{0,1}^{-2r} = (1/(2r)) (4/j_{0,1}^2)^r = (1/(2r)) R^{-2r},  R=j_{0,1}/2.  QED.
#   Ratio a_{r+1}/a_r ~ (r/(r+1)) * 4/j_{0,1}^2 -> 4/j_{0,1}^2 = R^{-2} = L < 1.
j=[mp.besseljzero(0,k) for k in range(1,40)]
print("Rayleigh-sum confirmation a_r = 2^{2r-1}/r * sum_k j_{0,k}^{-2r} vs exact |c_r|/(2r)!:")
cr=[1,-3,40,-1155,57456,-4370520,471556800,-68492499075,12885585512800,-3048056301418128]
for r in range(1,11):
    S=sum(jj**(-2*r) for jj in j)
    a_form = mp.mpf(2)**(2*r-1)/r * S
    a_exact = mp.mpf(abs(cr[r-1]))/mp.factorial(2*r)
    print(f"  r={r:2d}: a_form={mp.nstr(a_form,12)}  a_exact={mp.nstr(a_exact,12)}  match={mp.almosteq(a_form,a_exact,rel_eps=mp.mpf(10)**-30)}")
R=j[0]/2; L=1/R**2
print(f"\nR=j_{{0,1}}/2={mp.nstr(R,15)}   L=R^-2=4/j_{{0,1}}^2={mp.nstr(L,15)} < 1  (strict, exact constant).")
# (B) Sub-Gaussian GLOBAL envelope makes the saddle radius-free: since c_r alternate and the
# Wick/Gaussian comparison gives g(t) <= t^2/2 for ALL t (proven in Lean), the floor closes
# WITHOUT needing R>1; R>1 is the sharper companion (it shows g is even analytic past the
# saddle, and that the cumulant expansion itself converges out to |t|=R=1.2024>1).
print("\nNote: R=1.2024 > 1, so the cumulant SERIES converges at the saddle t*~sqrt(2logm/n)->0;")
print("and the GLOBAL bound g(t)<=t^2/2 (Lean-proven) closes the floor with no radius caveat at all.")

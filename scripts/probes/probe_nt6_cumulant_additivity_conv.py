from fractions import Fraction as Fr
from math import factorial as fac
def bc(k): return Fr(1,fac(k)**2)
# cpow as in Lean: cpow b 0 r = (1 if r==0 else 0); cpow b (m+1) r = sum_{i in range(r+1)} cpow b m i * b(r-i)
def cpow(c, m, r):
    if m==0: return Fr(1) if r==0 else Fr(0)
    return sum(cpow(c,m-1,i)*c(r-i) for i in range(r+1))
# We want a provable per-step inequality WITHOUT derivative. Direct: prove
#   (r+1) * cpow b (m+1) (r+1) <= (m+1) * cpow b (m+1) r ??? -- test the +1 indexing matching cpow recursion
# Actually let me just directly target the clean statement on cpow b m:
#   for m>=1:  (r+1)* cpow b m (r+1) <= m * cpow b m r.
# Provable route via induction on m using the recursion cpow b (m+1) = cpow b m  CONV  b.
# Key sublemma to prove first (m=1 base, single coeff): (k+1)*b(k+1) <= b(k).
for k in range(8):
    print(f"k={k}: (k+1)*bc(k+1)={float((k+1)*bc(k+1)):.5f} <= bc(k)={float(bc(k)):.5f} : {(k+1)*bc(k+1)<=bc(k)}")
print()
# Now the inductive step. Suppose (r+1) cpow b m (r+1) <= m cpow b m r  (IH for m).
# Want (r+1) cpow b (m+1) (r+1) <= (m+1) cpow b (m+1) r.
# cpow b (m+1) s = sum_{i=0}^{s} cpow b m i * b(s-i).
# Let A_m(s)=cpow b m s.  C(s):=A_{m+1}(s)= sum_{i=0}^s A_m(i) b(s-i).
# (r+1) C(r+1) =? <= (m+1) C(r).
# Test whether the clean PRODUCT inequality holds: is it true that for two sequences u,v with
#  (k+1)u_{k+1}<=a u_k and (k+1)v_{k+1}<=c v_k (and u,v>=0), the convolution w=u*v satisfies
#  (r+1)w_{r+1} <= (a+c) w_r ?   (the "additivity of the log-derivative bound" = cumulant additivity!)
# This is EXACTLY cumulant additivity. Test it on u=A_m (bound m), v=b (bound 1) => a+c=m+1. 
def conv(u,v,R): return [sum(u[i]*v[r-i] for i in range(r+1)) for r in range(R+1)]
import random
for trial in range(5):
    R=7
    # random nonneg decreasing-ratio sequences
    # build u with (k+1)u_{k+1}<= a u_k
    a=random.randint(1,4); c=random.randint(1,4)
    u=[Fr(random.randint(1,5))]
    for k in range(R):
        # pick u_{k+1} <= a u_k/(k+1)
        mx = a*u[k]/Fr(k+1)
        u.append(mx*Fr(random.randint(0,100),100))
    v=[Fr(random.randint(1,5))]
    for k in range(R):
        mx=c*v[k]/Fr(k+1)
        v.append(mx*Fr(random.randint(0,100),100))
    w=conv(u,v,R)
    ok=all((r+1)*w[r+1] <= (a+c)*w[r] for r in range(R))
    print(f"trial {trial}: a={a} c={c} conv satisfies (r+1)w_{{r+1}}<=(a+c)w_r : {ok}")

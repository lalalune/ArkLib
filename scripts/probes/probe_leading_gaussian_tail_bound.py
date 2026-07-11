"""
PROBE CLAIM E (the brick to formalize): the LEADING char-0 term obeys the Gaussian-tail bound RIGOROUSLY.

Leading term L_r := r! * fallingfac(n,r) = r! * n^r * prod_{j=0}^{r-1}(1 - j/n)  (j=0 term is 1).
                  = r! * n^r * prod_{j=1}^{r-1}(1 - j/n).

CLAIM E:  L_r <= Wick * exp(-r(r-1)/(2n))    where Wick = (2r-1)!! * n^r.
Proof skeleton (fully provable, no open input):
  L_r / Wick = [r! / (2r-1)!!] * prod_{j=1}^{r-1}(1-j/n)
             <= 1 * exp(-r(r-1)/(2n))                 [since r! <= (2r-1)!! and CLAIM B]
So the Gaussian-tail FACTOR that the machine FITTED for A_r is RIGOROUS for the leading term L_r.

Also confirm the two sub-facts:
  (B)  prod_{j=1}^{r-1}(1-j/n) <= exp(-r(r-1)/(2n))
  (F)  r! <= (2r-1)!!     (i.e. r!/(2r-1)!! <= 1)
"""
import math

def dfac(k):
    r = 1
    for i in range(1, 2 * k, 2):
        r *= i
    return r

def fallingfac(n, r):
    p = 1
    for j in range(r):
        p *= (n - j)
    return p

def falling_prod(n, r):
    p = 1.0
    for j in range(1, r):
        p *= (1 - j / n)
    return p

print("CLAIM E: L_r <= Wick * exp(-r(r-1)/2n)   (leading char-0 term obeys Gaussian-tail bound):")
print(f"{'n':>4} {'r':>2} {'L_r/Wick':>10} {'exp(-r(r-1)/2n)':>16} {'E holds':>8} {'r!<=(2r-1)!!':>12}")
allE = allF = allB = True
for n in [16, 32, 64, 128, 256, 1024]:
    for r in range(2, n):
        LoverW = (math.factorial(r) / dfac(r)) * falling_prod(n, r)
        gt = math.exp(-r * (r - 1) / (2 * n))
        e_ok = LoverW <= gt + 1e-12
        f_ok = math.factorial(r) <= dfac(r)
        b_ok = falling_prod(n, r) <= gt + 1e-12
        if not e_ok: allE = False
        if not f_ok: allF = False
        if not b_ok: allB = False
        if n in (16, 64) and r <= 8:
            print(f"{n:>4} {r:>2} {LoverW:>10.5f} {gt:>16.5f} {str(e_ok):>8} {str(f_ok):>12}")
print()
print(f"CLAIM B (falling <= gaussiantail)  all tested: {allB}")
print(f"CLAIM F (r! <= (2r-1)!!)           all tested: {allF}")
print(f"CLAIM E (L_r <= Wick*gaussiantail) all tested: {allE}")

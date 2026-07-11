"""
#407 LANE A2 — quantify the DENSITY of prize-regime corruptions for n=32, to settle
whether the super-poly per-U threshold c(n) actually corrupts the COUNT delta* depends on.

The per-U threshold is super-poly, but corruptions are rare. The count-relevant quantity is
   #spurious(q) = #{ U at width w : char-0 e2 != 0  but  e2 == 0 mod q (some labeling) }.
Heuristic: for fixed q (split, ~n^4), a "random" U has relation norm N_U of size ~ B=(n^2)^(n/2);
P(q | N_U) ~ (1/q) * (#distinct ways) ~ O(deg/q) = O(n / q). With C(n,w) ~ 2^n / sqrt(n) sets,
expected #spurious(q) ~ C(n,w) * n / q. For n=32, w=16: C(32,16)~6e8, q~n^4=1e6 => ~6e8*32/1e6
~ 2e4 expected spurious -- NOT negligible! (vs char-0 count which is small). Let's MEASURE.

Approach: instead of sampling U (misses rare hits), we FIX a moderate split prime q and count
EXACTLY how many width-w U are spurious, for a tractable n where we can enumerate (n<=16 exact),
then extrapolate the SCALING #spurious(q) ~ A * C(n,w) / q to predict n=32.

We also re-examine: at n=16 the count threshold = locus threshold = c(16). Is that because
#spurious(q) drops below 1 exactly at q > c(16)? For q just below c(16), #spurious(q) should be
small (1-2 U). Let's tabulate #spurious(q) vs q at n=16 to extract the law, then predict whether
n=32 at prize q has #spurious >> char-0 count (=> count corrupted) or ~0.
"""
import itertools, math
from sympy import symbols, Poly, cyclotomic_poly, ZZ, primitive_root, isprime, primerange

X = symbols('X')
def phi(n): return Poly(cyclotomic_poly(n, X), X, domain=ZZ)

def char0_e2zero_set(n, w):
    """exact char-0 e2=0 locus (e1!=0) at width w."""
    Phi = phi(n); out = set()
    for U in itertools.combinations(range(n), w):
        e1 = Poly(sum(X**i for i in U), X, domain=ZZ) % Phi
        if e1.is_zero: continue
        s = Poly(sum(X**i for i in U), X, domain=ZZ)
        R = (s*s - Poly(sum(X**(2*i) for i in U), X, domain=ZZ)) % Phi
        if R.is_zero: out.add(frozenset(U))
    return out

def fp_e2zero_count(n, w, q):
    g = pow(primitive_root(q), (q-1)//n, q)
    mu = [pow(g,j,q) for j in range(n)]
    out = set()
    for U in itertools.combinations(range(n), w):
        S=[mu[i] for i in U]; e1=sum(S)%q
        if e1==0: continue
        p2=sum((x*x)%q for x in S)%q
        if (e1*e1-p2)%q==0: out.add(frozenset(U))
    return out

# n=16: #spurious(q) = |fp locus| - |char-0 locus capped in fp| , tabulated vs q
n=16; w=8
c0 = char0_e2zero_set(n, w)
print(f"=== n=16, w=8: #spurious(q) = (F_q e2=0 width-8 sets) minus (char-0 sets) ===")
print(f"  char-0 e2=0 count (e1!=0) = {len(c0)}")
print(f"  {'q':>7} {'beta':>5} {'|fp locus|':>11} {'#spurious=|fp\\c0|':>17} {'#lost=|c0\\fp|':>13}")
qs = [p for p in primerange(17, 6000) if (p-1)%n==0]
data=[]
for q in qs:
    fp = fp_e2zero_count(n,w,q)
    spur = len(fp - c0); lost = len(c0 - fp)
    data.append((q, spur))
    if q<=2200 or spur>0:
        print(f"  {q:>7} {math.log(q)/math.log(n):>5.2f} {len(fp):>11} {spur:>17} {lost:>13}")

# fit #spurious(q) ~ A * C(n,w)/q on the q where spurious>0
pts = [(q,s) for q,s in data if s>0]
if pts:
    Cnw = math.comb(n,w)
    A = sum(s*q/Cnw for q,s in pts)/len(pts)
    print(f"\n  fit: #spurious(q) ~ A*C(n,w)/q with A~{A:.2e} (C({n},{w})={Cnw})")
    # last q with spurious>0 = c(16):
    print(f"  largest q with #spurious>0 = {max(q for q,s in pts)} (=c16=1873)")
    # predict n=32 at prize q
    n2=32; w2=16; C2=math.comb(n2,w2)
    for beta in [4,5,8.31]:
        q2 = int(n2**beta)
        pred = A*C2/q2
        print(f"  PREDICT n=32 w=16 at q~n^{beta}={q2}: #spurious ~ A*C(32,16)/q ~ {pred:.2e}")
    print(f"  (char-0 count at n=32,w=16 is small ~O(n^2)=~1000s; compare to predicted #spurious)")

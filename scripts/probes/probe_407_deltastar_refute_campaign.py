#!/usr/bin/env python3
"""
#407 P2 RUTHLESS REFUTATION CAMPAIGN — attack every candidate closed-form delta* / list-size
bound against the EXACT in-tree far-line-incidence governing law.

GOVERNING LAW (in-tree, exact; FarCosetExplosion.epsMCA_ge_far_incidence + badScalars_eq_explainable):
  for a FAR monomial direction u1=x^b, offset u0=x^a over mu_n in F_p,
    I(a,b; r) = #{ gamma in F_p : x^a + gamma*x^b on mu_n agrees with SOME RS[mu_n,k] codeword
                  on >= n-r points }
  delta* = ( max r in the valid far-window [k+1, n-k-1] with  max over far pencils I(a,b;r) <= budget )/n,
  prize budget = q*eps* = (n*2^128)*2^-128 = n.
I is computed WITHOUT codeword enumeration (no sqrt-loss): for each agreement set R (|R|=n-r),
the membership  x^a|_R + gamma x^b|_R in col(Vandermonde_R)  is AFFINE in gamma via the left
null space P of V_R, so R contributes ALL gamma (heavy) or <=1 gamma.

PRIZE DIRECTION: proper subgroup mu_n (n=2^mu) of F_p*, n | p-1, p PRIME, p >> n^3 (char-0-faithful).
delta* is verified char-faithful (identical maxI & binders) across multiple such primes.

EXACT GROUND TRUTH measured by this engine (budget=n):
  n=16 k=1 rho=1/16: delta*=0.6875  (Johnson 0.7500, cap 0.9375)  -> BELOW Johnson
  n=16 k=2 rho=1/8 : delta*=0.6250  (Johnson 0.6464, cap 0.8750)  -> BELOW Johnson
  n= 8 k=1 rho=1/8 : delta*=0.6250  (Johnson 0.6464)              -> BELOW Johnson
  n=16 k=4 rho=1/4 : delta*=0.5625  (Johnson 0.5000, cap 0.7500)  -> ABOVE Johnson (the +1 rung)
  n= 8 k=2 rho=1/4 : delta*=0.3750  (Johnson 0.5000)              -> BELOW Johnson
  n= 8 k=4, n=16 k=8 rho=1/2: far-window [k+1,n-k-1] EMPTY -> NO beyond-Johnson r (delta*<=Johnson)

VERDICTS (see refute_table()):
  REFUTED  Kambire edge 1-rho-2rho ln(1/2rho)/log2(q eps*): overshoots exact delta* at 5/5 points by
           0.10-0.26 (margin does NOT shrink with n); at rho=1/2 predicts 0.5>Johnson where the window
           is empty. Predicts substantially MORE proximity than the law permits.
  REFUTED  Entropy pin 1-rho-H(rho)/(beta log n) (beta=1): overshoots; and is monotone in rho while the
           exact (delta*-Johnson) FLIPS sign -> no single beta fixes it (only a fitted beta(n,rho)).
  REFUTED  "always beyond Johnson" / monotone clean form: sign(delta*-Johnson) FLIPS over the sweep.
  REFUTED  list ~ 2(n-a)+1: the binding incidence is a STEP (O(1)/O(n) below crossover, >>budget above),
           not ~2r+1 near the crossover.
  SURVIVES only: |delta* - (1-sqrt(rho))| <= 1/n on the entire sweep (delta* = Johnson +- one rung).
           This is the lone clean relation -> it says there is NO simple beyond-Johnson closed form;
           the gain over Johnson (if any) is sub-rung at these n. Consistent with the prize being OPEN.

This is a REFUTATION probe, not a proof. It does not establish any delta* lower bound at prize scale
(n=2^mu, mu>=10); it computes the EXACT law at small computable n and shows no clean closed form survives.
Full enumeration is O(C(n, n-r)) per pencil -> only n<=16 (and rho=1/2 trivially) are fully feasible.
"""
import sys, math, itertools
sys.path.insert(0, 'scripts/probes')
from prize_workspace import get_W

def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and all(p % d for d in range(2, int(p**0.5) + 1)):
            return p
        p += n

def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0; pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p); rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows

def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k + j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def incidence(S, p, k, a, b, r, stop_above=None):
    """exact far-line incidence I(a,b;r); early-exits once count exceeds stop_above (verdict-only)."""
    n = len(S); size = n - r
    if size <= k: return p, True
    pa_ = [pow(int(x), a, p) for x in S]; pb_ = [pow(int(x), b, p) for x in S]
    good = set()
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null(V, p)
        if not P: continue
        pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa): return p, True
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))): good.add(g)
        if stop_above is not None and len(good) > stop_above and stop_above < p:
            return len(good), False
    return len(good), False

def max_far_incidence(S, p, k, r, budget=None):
    n = len(S); size = n - r; best = (-1, None)
    for b in range(k, size):
        for a in range(n):
            if a == b: continue
            c, _ = incidence(S, p, k, a, b, r, stop_above=budget)
            if c > best[0]: best = (c, (a, b))
            if budget is not None and best[0] > budget: return best  # known BAD
    return best

def delta_star_exact(n, k, p, budget):
    """EXACT delta* via downward scan (incidence increases with r => first GOOD from top is delta*)."""
    S = list(get_W(n, p).S); first_good = None; profile = []
    for r in range(n - k - 1, k, -1):           # valid far-window: size=n-r in (k, n-k)
        mx, st = max_far_incidence(S, p, k, r, budget)
        profile.append((r, mx, st, mx <= budget))
        if mx <= budget: first_good = r; break
    return (first_good / n if first_good else 0.0), profile

# ---------- candidate closed-forms ----------
def Hbin(x):
    if x <= 0 or x >= 1: return 0.0
    return -x*math.log2(x) - (1-x)*math.log2(1-x)
def kambire(rho, blog2):          # Kambire edge; q*eps*~n => log2(q eps*)=log2 n
    return 1 - rho - 2*rho*math.log(1.0/(2*rho))/blog2 if blog2 > 0 else None
def entpin(rho, n, beta=1.0):     # entropy pin
    return 1 - rho - Hbin(rho)/(beta*math.log2(n))

# Ground truth measured by delta_star_exact above (recomputable via --compute):
GT = [(16,1,0.6875),(16,2,0.6250),(8,1,0.6250),(16,4,0.5625),(8,2,0.3750)]

def refute_table():
    print("="*88)
    print("REFUTATION: candidates vs EXACT far-line-incidence delta* (budget=n, p>>n^3)")
    print("="*88)
    print(f"{'n':>3}{'k':>3}{'rho':>7}{'delta*':>9}{'Johnson':>9}{'Kambire':>9}{'EntPin':>9}{'|d*-J|<=1/n':>13}")
    signs = []
    for (n,k,ds) in GT:
        rho=k/n; J=1-math.sqrt(rho); blog=math.log2(n)
        K=kambire(rho,blog); H=entpin(rho,n)
        within = abs(ds-J) <= 1.0/n + 1e-9
        signs.append('+' if ds>J+1e-9 else ('-' if ds<J-1e-9 else '0'))
        print(f"{n:>3}{k:>3}{rho:>7.4f}{ds:>9.4f}{J:>9.4f}{K:>9.4f}{H:>9.4f}{str(within):>13}")
    print(f"\nKambire overshoots exact delta* at {sum(1 for (n,k,ds) in GT if kambire(k/n,math.log2(n))>ds+1/n)}/{len(GT)} pts -> REFUTED.")
    print(f"sign(delta*-Johnson) = {signs} (FLIPS) -> no monotone/'always beyond Johnson' form -> REFUTED.")
    print(f"|delta* - (1-sqrt rho)| <= 1/n holds at ALL pts -> SURVIVOR (= 'Johnson +- one rung', no clean gain form).")

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--compute':
        for (n,k) in [(8,1),(8,2),(16,1),(16,2),(16,4)]:
            p = find_prime_cong1(n, max(200003, n**3+1))
            ds, prof = delta_star_exact(n, k, p, n)
            J=1-math.sqrt(k/n)
            print(f"n={n} k={k} rho={k/n:.4f} p={p}: EXACT delta*={ds:.4f} (Johnson {J:.4f})  profile={prof}")
    else:
        refute_table()

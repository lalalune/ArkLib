from math import comb
from fractions import Fraction

def specCount(m, r):
    top = min(r, 2*m - r)
    s = 0
    for k in range(0, top+1):
        if k % 2 == r % 2:
            s += comb(m, k) * (2**k)
    return s

print("=== survival ratio N_r/C(n,r) at binding depth r=log2(n), n=2^a ===")
print(f"{'a':>3}{'n':>9}{'r':>4}{'frac=slack/C':>16}{'surv=N/C':>12}{'dec?':>6}")
prev_frac = None
fracs = []
for a in range(3, 22):
    n = 2**a
    m = n//2
    r = a
    C = comb(n, r)
    N = specCount(m, r)
    slack = C - N
    frac = Fraction(slack, C)
    surv = Fraction(N, C)
    fracs.append((n, frac, surv, C, N, slack))
    dec = ""
    if prev_frac is not None:
        dec = "DEC" if frac < prev_frac else ("INC" if frac > prev_frac else "EQ")
    print(f"{a:>3}{n:>9}{r:>4}{float(frac):>16.7f}{float(surv):>12.7f}{dec:>6}")
    prev_frac = frac

print("\n=== frac strictly decreasing for all n>=16 tested? ===")
allmono = True
firstfail = None
for i in range(1, len(fracs)-1):
    n1,f1 = fracs[i][0], fracs[i][1]
    n2,f2 = fracs[i+1][0], fracs[i+1][1]
    if n1 < 16: continue
    if not (f1 > f2):
        allmono = False
        if firstfail is None: firstfail = (n1,n2)
print("strictly decreasing all n>=16:", allmono, "firstfail:", firstfail)

# leading-term model: dominant term k=r (since r=log2 n << m). N_r ~ C(m,r) 2^r.
print("\n=== leading-term: lead=C(m,r)2^r,  N/lead -> 1?  lead/C -> survival? ===")
for a in range(3,22):
    n=2**a; m=n//2; r=a
    C=comb(n,r); N=specCount(m,r)
    lead = comb(m,r)*(2**r)
    print(f"n={n:>9} r={r:>3}  N/lead={float(Fraction(N,lead)):.7f}  lead/C={float(Fraction(lead,C)):.7f}  surv=N/C={float(Fraction(N,C)):.7f}")

# The clean comparison: C(m,r)2^r vs C(n,r), n=2m.
# C(2m,r) = prod_{i=0}^{r-1}(2m-i)/(r!).  C(m,r)2^r = 2^r prod (m-i)/r! = prod (2m-2i)/r!.
# ratio lead/C = prod_{i=0}^{r-1} (2m-2i)/(2m-i) = prod (1 - i/(2m-i)).
# So survival ~ prod_{i=0}^{r-1} (1 - i/(2m-i)).  As m->inf with r=log2(2m)=a:
#   each factor ->1, and sum_{i} i/(2m) ~ r^2/(4m) = a^2/(2n) -> 0. So product ->1.
print("\n=== EXACT identity check: lead = C(m,r)2^r and lead/C = prod_{i<r}(2m-2i)/(2m-i) ===")
for a in range(3,12):
    n=2**a; m=n//2; r=a
    C=comb(n,r); lead=comb(m,r)*(2**r)
    prod = Fraction(1)
    for i in range(r):
        prod *= Fraction(2*m-2*i, 2*m-i)
    print(f"n={n:>6} r={r}: lead/C={Fraction(lead,C)}  prod={prod}  match={Fraction(lead,C)==prod}")

# Is N_r itself >= lead always (lead is the single top term, all terms positive)? yes by construction.
# And N_r <= ? Need an UPPER bound on N_r to lower-bound survival... actually we want survival->1,
# i.e. N_r/C -> 1. We have N_r >= lead, and lead/C -> 1. So N_r/C -> 1 IF N_r/C <= 1 (it is, N<=C) AND lead/C->1.
# So: lead <= N_r <= C, and lead/C -> 1  ==>  N_r/C -> 1 (squeeze). The provable brick: N_r >= C(m,r)2^r
# (drop all but top term) and C(m,r)2^r / C(2m,r) -> 1, i.e. slack/C <= 1 - lead/C -> 0.
print("\n=== squeeze check: lead <= N_r <= C(2m,r) at every tower level ===")
ok=True
for a in range(3,22):
    n=2**a; m=n//2; r=a
    C=comb(n,r); N=specCount(m,r); lead=comb(m,r)*(2**r)
    if not (lead <= N <= C): ok=False
print("lead <= N_r <= C all levels:", ok)

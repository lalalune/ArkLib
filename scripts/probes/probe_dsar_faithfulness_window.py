import math
# ============================================================================
# probe_dsar_faithfulness_window.py  (DSAR route: char-0 Wick exact + faithfulness threshold)
#
# ESTABLISHED in-tree (axiom-clean Lean):
#  (C0)  CHAR-0:  E_r(mu_n) <= (2r-1)!! n^r          gaussianEnergyBound_dyadic  (UNCONDITIONAL)
#  (DC)  CHAR-p:  E_r(mu_n) >= n^{2r}/q              energy_ge_dc                (DC lower bound)
#  ==>   char-p Wick bound E_r<=(2r-1)!! n^r is NECESSARILY FALSE when n^{2r}/q > (2r-1)!! n^r,
#        i.e. when  n^r > q (2r-1)!!.   (not_gaussianEnergyBound_of_card_pow_gt)
#
# So the FAITHFULNESS THRESHOLD T(n,r) (smallest q for which char-p Wick CAN hold) satisfies the
# HARD NECESSARY lower bound  T(n,r) >= n^r / (2r-1)!!.   This is a PROVEN obstruction, not a guess.
#
# MY ROUTE QUESTION: is there ANY depth r at which BOTH
#   (a) char-p Wick at the prize q is NOT yet refuted by the DC obstruction  (q >= n^r/(2r-1)!!), AND
#   (b) the moment-method sup bound it yields,  M <= ( q (2r-1)!! n^r )^{1/2r},
#       beats the prize target  C sqrt(n log q) ?
# If NO r satisfies both -> the char-0->char-p route has NO ESCAPE; it reduces to the BGK Wick wall.
# ============================================================================

def logdfact(k):  # log of (k)!! for odd k = log (2r-1)!!
    s = 0.0
    while k > 1:
        s += math.log(k); k -= 2
    return s

def analyze(a, beta):
    n = 2.0**a
    q = n**beta
    lnn = math.log(n); lnq = math.log(q)
    print(f"\n=== n=2^{a}={int(n)}, q=n^{beta}={q:.3e}, ln q={lnq:.2f} ===")
    print(f"prize target M_prize = C*sqrt(n ln q) ~ sqrt(n ln q) = {math.sqrt(n*lnq):.3e}  (C=1)")
    print(f"  r   q_needed=n^r/(2r-1)!!   q>=needed?   Mbound=(q(2r-1)!!n^r)^(1/2r)   beats prize?")
    best_r = None; best_M = None
    rmax = max(4, int(2*lnq))
    for r in range(1, rmax+1):
        ldf = logdfact(2*r-1)
        log_qneed = r*lnn - ldf                       # ln( n^r/(2r-1)!! )
        faithful_ok = (lnq >= log_qneed)              # q >= n^r/(2r-1)!!  (DC obstruction NOT triggered)
        # moment sup bound: M^{2r} <= q*(2r-1)!!*n^r  => log M = (lnq + ldf + r lnn)/(2r)
        logM = (lnq + ldf + r*lnn) / (2*r)
        beats = (logM < 0.5*(lnn+math.log(lnq)))      # M < sqrt(n ln q)
        if faithful_ok:
            if best_M is None or logM < best_M:
                best_M = logM; best_r = r
        flag_f = "OK " if faithful_ok else "REFUTED"
        flag_b = "yes" if beats else "no"
        mark = " <-- both" if (faithful_ok and beats) else ""
        print(f"  {r:3d}  ln(n^r/(2r-1)!!)={log_qneed:8.2f}  {flag_f}    lnM={logM:7.2f}  beats={flag_b}{mark}")
    if best_r is not None:
        print(f"  >> best FAITHFUL r={best_r}: lnM={best_M:.2f}, M={math.exp(best_M):.3e}; "
              f"prize sqrt(n ln q)={math.sqrt(n*lnq):.3e}  "
              f"=> route {'WINS' if best_M < 0.5*(lnn+math.log(lnq)) else 'LOSES (>=prize)'}")
    else:
        print("  >> NO faithful r at all (DC obstruction refutes char-p Wick at EVERY depth).")

# the prize regime: n=2^30, p ~ n^4 (beta in [3,4]); also smaller for the visible crossover
for a, beta in [(3,4),(6,4),(8,4),(12,4),(20,4),(30,4),(30,3)]:
    analyze(a, beta)

print("\n" + "="*70)
print("INTERPRETATION:")
print(" The faithful window is r <= r*(n,q) where n^r <= q(2r-1)!!, i.e. r ln n <= ln q + ln(2r-1)!!.")
print(" Since (2r-1)!! <= (2r)^r, faithful requires roughly  r (ln n - ln(2r)) <= ln q,")
print(" so for n >> (2r)^2 only SHALLOW r are faithful; but shallow r give a WEAK sup bound")
print(" M <= (q n^r (2r-1)!!)^{1/2r} ~ q^{1/2r} sqrt(2rn), which needs DEEP r (~ln q) to kill q^{1/2r}.")
print(" The two requirements PULL OPPOSITE: faithfulness caps r from above (~ln q/ln(n)), the sup")
print(" bound needs r from below (~ln q). They meet only when ln n ~ O(1), i.e. tiny n. For prize")
print(" n=2^30 the faithful r* is O(1) and the resulting M is ~q^{1/2r*} = HUGE >> sqrt(n ln q).")

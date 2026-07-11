import numpy as np
# Prize regime: tau = n = p^{1/beta}, beta in [4,5]. m=(p-1)/n=2^128 fixed at prize.
# Target: M(n) <= C sqrt(n log(p/n)).
# OSV applicability wall: Theorem 1.1 + Lemma 3.7 require tau >= p^{3/7+eps}.  3/7=0.42857
# Lemma 3.6 (Shkredov, the ONLY r=1 statement, = our case f=bX): S <= min(sqrt p, sqrt(tau) p^{1/6} (log p)^{1/6}).

print("=== A) Is OSV curve method (Thm1.1 / Lem3.7) even applicable in prize regime? ===")
print(f"{'beta':>5} {'tau=p^(1/b)':>12} {'thresh p^(3/7)':>14} {'applicable?':>12}")
for beta in [2.0, 2.33, 7/3, 2.5, 3, 4, 5]:
    inv = 1.0/beta
    print(f"{beta:5.2f} {inv:12.4f} {3/7:14.4f} {'YES' if inv>=3/7 else 'NO (vacuous)':>12}")

print()
print("Conclusion: prize beta in [4,5] => exponent 1/beta in [0.20,0.25] << 3/7=0.4286.")
print("OSV curve method is VACUOUS in prize regime (it's built for p^{3/7} < tau < p^{3/4}).")
print()

print("=== B) Shkredov r=1 bound (Lemma 3.6) vs target, prize regime ===")
# We need to know the constant; Shkredov's S <= sqrt(tau) p^{1/6}(log p)^{1/6} up to absolute const.
# Compare EXPONENT-wise to target sqrt(n log(p/n)) ~ sqrt(n) * sqrt(log m) where m=p/n.
# tau=n=p^{1/beta}. Shkredov ~ p^{1/(2beta)} * p^{1/6}.  Target ~ p^{1/(2beta)} * sqrt(log).
print(f"{'beta':>5} {'sqrt(tau) exp':>13} {'Shkredov exp':>13} {'target exp':>11} {'Shk beats triv tau?':>20}")
for beta in [2.0, 7/3, 3, 4, 5]:
    e_sqrt_tau = 1/(2*beta)         # log-p exponent of sqrt(n)
    e_shk = 1/(2*beta) + 1/6        # log-p exponent of shkredov main term (ignore loglog)
    e_triv = 1/beta                 # trivial bound tau=n
    # Shkredov nontrivial iff e_shk < e_triv  <=> 1/6 < 1/(2beta) <=> beta < 3
    print(f"{beta:5.2f} {e_sqrt_tau:13.4f} {e_shk:13.4f} {e_sqrt_tau:11.4f} {'YES' if e_shk< e_triv else 'NO (>= trivial)':>20}")
print()
print("Shkredov nontrivial iff beta<3 (since 1/6 < 1/(2beta) needs beta<3).")
print("Prize beta in [4,5]: Shkredov exponent 1/(2b)+1/6 vs trivial 1/b -> 1/6 > 1/(2b), VACUOUS too.")

"""
R2 CORRECTED optimization: Kambire FIXES the rate rho = k/n = (r-2)/s.  Under this constraint,
r and s are COUPLED: r = rho*s + 2.  The construction then maximizes closeness-to-capacity
eta = (1-rho)-delta = 2/s by taking s as LARGE as possible, subject to the count >= eps*q.

So the optimization is NOT free over (s,r): it is
   maximize  (closeness 2/s, i.e. minimize 1/s)  <=>  maximize s
   subject to  r = rho*s+2  AND  count |H^{(+r)}(mu_s)| >= eps*q  AND  s | n.
But larger s makes BOTH eta smaller (good, closer to capacity) AND the count larger (good).
Wait -- larger s gives MORE closeness AND MORE count, so why is there a threshold?

Re-read: the prize fixes eps* = 2^-128 and asks for the SUP delta at which gaps fail with
loss eps*.  Kambire delivers count = (1/2rho)^{rho s} bad scalars.  The prize threshold is
count >= eps* * q (so the proximity-loss is <= eps*).  Larger s => more count => satisfies it
more easily => can push eta=2/s smaller => delta closer to capacity.  The BINDING constraint is
the FIELD SIZE: count <= q (can't have more bad scalars than field elements roughly), and the
prime must exist (Linnik: p < n^A, p ~ 1 mod n).  Kambire's window p in [4^s, 8^s] => log2 p ~
2s..3s.  And rho*s*log2(1/2rho) = log2(count) <= log2 q ~ 2s..3s.  So s is bounded by the
field-fit: rho*log2(1/2rho) <= log2 q / s ~ const.  THAT pins s.

Correct threshold (count = eps* q, the prize's exact pin):
   rho*s*log2(1/2rho) = log2(eps* q) = log2 q - 128.
   With Kambire's q ~ p ~ 8^s = 2^{3s} (top of his window): log2 q = 3s.
   => rho*s*log2(1/2rho) = 3s - 128  => s*(3 - rho*log2(1/2rho)) = 128  => s = 128/(3-rho log2(1/2rho)).
That's the worst-case s.  Let's compute it and the resulting (m,r,s,delta*).
"""
import math
def worst_case(rho, eps_bits=128, logq_over_s=3.0):
    # count = (1/2rho)^{rho s} = eps* q ; with log2 q = logq_over_s * s  (Kambire window top 8^s)
    A = rho*math.log2(1/(2*rho))
    # rho s log2(1/2rho) = logq_over_s*s - eps_bits  => s(logq_over_s - A) = eps_bits
    denom = logq_over_s - A
    if denom <= 0:
        return None
    s = eps_bits/denom
    r = rho*s + 2
    delta = 1 - r/s
    eta = 2/s
    logq = logq_over_s*s
    log2count = A*s
    return dict(s=s, r=r, delta=delta, eta=eta, logq=logq, log2count=log2count,
                log2_epsq=logq-eps_bits, m_over_n="m=n/s")

print("R2 worst-case (s,r) under Kambire's rate constraint rho=(r-2)/s and count=eps*q at window top q~8^s:")
print("="*100)
for rho in [0.5,0.25,0.125,0.0625]:
    for lqs in [2.0,3.0]:  # q between 4^s and 8^s
        wc = worst_case(rho, 128, lqs)
        if wc is None:
            print(f" rho={rho} logq/s={lqs}: NO solution (rho log2(1/2rho) >= logq/s) -- count exceeds field"); continue
        print(f" rho={rho:6} q~{2**0}^... logq/s={lqs}: s*={wc['s']:8.1f}  r*={wc['r']:8.1f}  "
              f"r*/log2: depends on n | delta*={wc['delta']:.5f}  eta=2/s={wc['eta']:.6f}  "
              f"log2(count)={wc['log2count']:.1f}=log2(eps*q)={wc['log2_epsq']:.1f}")
print()
print("KEY: the worst-case s* is a CONSTANT depending only on rho and eps_bits/(logq/s), NOT growing with n.")
print("  -> s* ~ 50-130 (small!), r* = rho*s*+2 = O(s*) = O(1) in n but ~ tens.  m = n/s* ~ n/const.")
print("This matches the KB 'prize sits at r~11, s~44' note for mu=30,rho=1/4.")

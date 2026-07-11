import numpy as np
# SYNTHETIC ALGEBRAIC SANITY CHECK (not an empirical tower computation).
# The QV bound Delta_i^2 <= log2*Delta_i is a DEDUCTIVE consequence of Delta_i in [0, log2];
# this script samples Delta_i directly inside that envelope and confirms the bound is
# consequence-true (it CANNOT catch a failing real subgroup because it does not compute rho_i).
# The envelope itself (rho_i in [sqrt2,2] on PROPER thin subgroups) is validated by the
# file-header probes probe_rho_increment_bounded.py / probe_rho_excess_growth.py, not here.
#
# QV prerequisite for Freedman: for increments Delta_i = log rho_i in [0, log2],
# the quadratic variation sum_{i<a} Delta_i^2 <= a*(log2)^2  (since 0<=Delta_i<=log2 => Delta_i^2<=(log2)^2).
# Also tighter: since Delta_i in [0,log2], Delta_i^2 <= log2 * Delta_i, so QV <= log2 * S_a.
# This is a TRIVIAL consequence of the bounds, but it IS the predictable-QV the Freedman step needs.
# Probe rho_i in [sqrt2, 2] (i.e. Delta_i in [0.5 log2, log2]) on PROPER thin subgroups to confirm
# the increment bounds the file relies on actually hold (re-confirm the [0,log2] envelope holds,
# so the QV bound is non-vacuous), and that QV <= a*(log2)^2 holds.
log2 = np.log(2)
def simulate(a, trials=2000):
    # model Delta_i as uniform in [0.5 log2, log2] (the measured ratio band rho in [sqrt2,2])
    fail_env = 0; fail_qv = 0; fail_tight = 0
    rng = np.random.default_rng(0)
    for _ in range(trials):
        d = rng.uniform(0.5*log2, log2, size=a)
        if np.any(d < -1e-12) or np.any(d > log2+1e-12): fail_env += 1
        qv = np.sum(d*d)
        if qv > a*log2*log2 + 1e-9: fail_qv += 1
        if qv > log2*np.sum(d) + 1e-9: fail_tight += 1
    return fail_env, fail_qv, fail_tight
for a in [4,8,16,32,64]:
    e,q,t = simulate(a)
    print("a=%d: envelope fails=%d | QV<=a(log2)^2 fails=%d | QV<=log2*S fails=%d" % (a,e,q,t))

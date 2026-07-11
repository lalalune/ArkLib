# Probe: the closed-form (L, V) instantiation clears the numeric budget of
# DeepBandSecondMoment.budget_of_numeric INTEGER-EXACTLY, for a sweep of params,
# with D the TRUE deep-pair count (not just the bound).
from itertools import combinations
from math import comb

def true_D(n, k, mm):
    r = k + mm + 1
    Ts = list(combinations(range(n), r))
    cnt = 0
    for T in Ts:
        sT = set(T)
        for T2 in Ts:
            if T2 != T and len(sT & set(T2)) > k:
                cnt += 1
    return cnt

ok = all_ok = True
for n, k, mm, q in [(6,1,1,7),(8,1,1,17),(8,2,1,17),(8,1,2,17),(10,3,1,11),(7,2,2,13)]:
    P = comb(n, k+mm+1)
    Cp = comb(k+mm+1, k+1) * comb(n-(k+1), mm)
    D = true_D(n, k, mm)
    assert D <= P * Cp, "deepPairs bound violated?!"
    M = 2*(k+mm+1)
    Q = q**(mm+1)
    Lam = P // Q + Cp + 2
    V = (P * Lam) // (q**mm)
    lhs = P*P*q**(M-(2*mm+1)) + (D+P)*q**(M-mm) + V*q**M
    rhs = 2*Lam*P*q**(M-mm)
    bound = V // (Lam*Lam)  # the resulting badSet lower bound
    print(f"n={n} k={k} m={mm} q={q}: P={P} C'={Cp} D={D} Λ={Lam} V={V} "
          f"budget={'OK' if lhs<=rhs else 'FAIL'} badSet≥{bound} (q={q})")
    all_ok &= (lhs <= rhs)
print("ALL BUDGETS CLEAR:", all_ok)

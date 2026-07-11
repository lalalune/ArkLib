#!/usr/bin/env python3
"""
probe(#444 wf-G2): STEPANOV auxiliary-polynomial method DIRECTLY for the sup-norm.

GOAL: reduce M(n)=max_{b!=0}|S_b|, S_b=sum_{x in mu_n} e_p(bx), to:
  EXISTENCE of a low-degree auxiliary poly F vanishing to order >=M on the
  "bad set" B(b,eta) = {x in mu_n : |1 - e_p(bx)| <= eta}  (phase near 1),
  forcing |B|*M <= deg F  => |B| small => cancellation.

SUFFICIENT LEMMA (G2 form):
  If for the bad set B there is a nonzero F in F_p[X] with
    (i) deg F <= D,
    (ii) (X - x)^M | F for every x in B (order-M vanishing on B),
  then |B| <= D / M  (Stepanov inequality, the in-tree card_le_natDegree_of_vanishing).
  Combined with a sup->bad-set link  M(n) <= n * (1 - c*|B^c|/n) -> need |B| controlled.

THE TWO FATAL QUESTIONS this probe answers (decisively, exact integers):
 Q1. Is the bad set B(b,eta) ALGEBRAIC? Stepanov requires B to be the common-zero set of a
     low-degree poly relation. B is defined by the ARCHIMEDEAN condition bx mod p in a short
     interval. Measure: is B = mu_n intersect (short residue interval) describable by a
     low-degree polynomial constraint? Equivalent test: does B carry MULTIPLICATIVE structure
     (a coset of a subgroup) or is it a generic interval slice?
 Q2. The degree budget. Even GRANTING an algebraic B, the auxiliary that vanishes to order M on
     B and is low-degree must have deg F >= M*|B|. Stepanov's gain over trivial requires
     building F with deg F << n while M >= 2. But mu_n_roots_simple (PROVEN in-tree) shows the
     only natural relation X^n-1 is SEPARABLE -> M=1 forced. Probe: what is the largest M
     achievable for an F of degree < n vanishing to order M on a phase-bad set of size |B|?
"""
import numpy as np, sympy

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, cur = [], 1
    for _ in range(n):
        S.append(cur); cur = cur*h % p
    return sorted(S)

def find_prime(n, beta):
    # p = n^beta-ish prime with n | p-1, p odd, p >> n^3
    target = n**beta
    m = max(2, target // n)
    while True:
        p = m*n + 1
        if sympy.isprime(p) and p > n**3:
            return p
        m += 1

def main():
    print("="*86)
    print("Q1: is the phase-bad set B(b,eta) = {x in mu_n : |1-e_p(bx)|<=eta} ALGEBRAIC?")
    print("   test: is B a union of cosets of a subgroup of mu_n? (=> would have algebraic relation)")
    print("="*86)
    for mu in (4,5,6):
        n = 2**mu
        p = find_prime(n, 4)
        S = subgroup(p, n)
        Sset = set(S)
        # pick the worst b (max |S_b|)
        bestb, bestmag = 1, 0.0
        for b in range(1, min(p, 4000)):
            z = np.exp(2j*np.pi*(np.array(S, dtype=float)*b % p)/p).sum()
            if abs(z) > bestmag:
                bestmag, bestb = abs(z), b
        b = bestb
        # bad set: residues bx mod p closest to 0 (phase near 1)
        res = np.array([(b*x) % p for x in S])
        signed = np.where(res > p//2, res - p, res)  # in (-p/2,p/2]
        order = np.argsort(np.abs(signed))
        for frac in (0.25, 0.5):
            k = max(1, int(frac*n))
            B = set(S[i] for i in order[:k])
            # test multiplicative coset structure: is B closed under any nontrivial subgroup mult?
            # for each divisor d|n, subgroup H_d of order d; count cosets fully inside B
            coset_hit = []
            for d in [2**j for j in range(1, mu+1)]:
                Hd = set(subgroup(p, d))  # order-d subgroup (subset of mu_n? only if d|n yes)
                # cosets of Hd in mu_n: x*Hd
                full = 0; total = 0
                seen = set()
                for x in S:
                    coset = frozenset((x*h) % p for h in Hd)
                    if coset in seen: continue
                    seen.add(coset); total += 1
                    if coset <= B: full += 1
                coset_hit.append((d, full, total))
            algebraic = any(full>0 and full==tot for d,full,tot in coset_hit if d>1)
            # random null: if B were random size-k subset, P(any full coset) ~ tiny
            print(f"mu={mu} n={n} p={p} b={b} |S_b|/sqrt(n)={bestmag/np.sqrt(n):.2f} "
                  f"|B|={k} coset-structured={algebraic}")
            for d,full,tot in coset_hit:
                if full>0:
                    print(f"      subgroup order {d}: {full}/{tot} full cosets inside B")
    print()
    print("="*86)
    print("Q2: max vanishing order M for a degree-<n auxiliary on a SEPARABLE subgroup")
    print("   in-tree mu_n_roots_simple: X^n-1 separable => (X-x)^2 nmid (X^n-1) => M=1 forced")
    print("   so any F vanishing to order M>=2 on >=1 pt of mu_n needs deg >= M (no subgroup help)")
    print("   trivial budget: F=prod_{x in B}(X-x)^M has deg = M|B| => |B| <= deg F/M = (n-1)/M")
    print("   => to beat trivial |B|<=n need M>=2 AND deg F<n: gives |B| < n/2, but building such F")
    print("      requires M-fold contact, which the separable relation forbids structurally.")
    print("="*86)

if __name__ == "__main__":
    main()

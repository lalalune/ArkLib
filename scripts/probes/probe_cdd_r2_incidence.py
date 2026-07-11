#!/usr/bin/env python3
"""CDD off-diagonal (r=2) reduction + self-refutation of a clean-formula hope.
DERIVATION (correct): via Jacobi->Gauss J(psi^a,psi^{s-a})=tau(psi^a)tau(psi^{s-a})/tau(psi^s)
+ orthogonality, A(s)=sum_{Sigma j = s} J(j) = m * sum_{c in mu_n} chi_s(c+1), so the CDD
off-diagonal sqrt-cancellation (r=2) <=> the subgroup incidence
  I = #{(c,c',d) in mu_n^3 : c+1 = d(c'+1)} = #{c - d c' = d - 1 : c,c',d in mu_n}.
SELF-REFUTATION: I looked clean (I=2n-3) on cherry-picked (even n, large p) instances,
but is FIELD-DEPENDENT/erratic on fuller data (n=5->9, 7->13, 9->21, 11->21, 13->33).
NO clean closed form => confirms swarm q-dependence (daf57ed35) + erratic orbit count
(ff42c6e54). The reduction is the contribution; the uniform-over-fields incidence bound
is the open core = CDD = Paley Graph / uniform Gauss-sum equidistribution."""

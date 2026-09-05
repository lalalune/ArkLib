# Derivative repair and the regular-solution incidence budget

Status: proved on paper, with finite transcription and arithmetic checks; not
Lean-formalized. This strengthens necessary conditions on full-source
universal factors. It does not improve the C2 score or exclude the binding flag.

## Factor-specific derivative repair

Use the full nonzero contact kernel and notation of
[the same-kernel descent note](astra_kernel_descent_2026-09-04.md). Let a nonzero
polynomial F divide every element of that kernel, with exact R degree `r>0`,
contact weight `c`, residual total `t`, and nodewise contact orders `ν_i`.
Assume `r<p=char K` and `w≥1`.

For every integer `1≤h≤r`, universality implies

```
Σ_i min(h,ν_i) > h(w-1).                                  (1)
```

To prove this, differentiate F h times in the original R coordinate. In local
coordinates `X=x_i+τ`, `Y=u0_i+Z u1_i+Rτ+v`, this derivative is the operator
`∂R-τ∂v`. With local weights `(τ,v,R,Z)=(1,2,0,0)`, each application lowers
minimum weight by at most one. Thus

```
contactOrder_i(∂R^h F) ≥ max(0,ν_i-h).
```

Put `L_h=∏_i(X-x_i)^min(h,ν_i)` and `P_h=L_h ∂R^h F`. Every contact order of
P_h is at least ν_i. Since `r<p`, the leading R coefficient survives ordinary
differentiation: its scalar multiplier is `r(r-1)…(r-h+1)≠0`. In particular,

```
P_h ≠ 0,
degree_R(P_h) = r-h,
residualTotal(P_h) ≤ t-h,
contactWeight(P_h) ≤ c-h(w-1)+Σ_i min(h,ν_i).
```

Suppose the sum in (1) were at most its right side. Choose a nonzero Q of
minimum R degree in the full kernel and write `Q=F Q'`. Minimum contact order
is additive on nonzero products, so Q' has order at least `max(0,m-ν_i)` at
node i. P_h Q' therefore retains every order-m contact. Maximum weighted
degree, residual total, and R degree are additive on nonzero products; hence

```
contactWeight(P_h Q') ≤ contactWeight(Q) < D,
residualTotal(P_h Q') ≤ residualTotal(Q)-h ≤ L,
degree_R(P_h Q') = degree_R(Q)-h < degree_R(Q) ≤ S.
```

The nonzero replacement is in the same full kernel and contradicts minimality.
This proves (1). The repair need only have smaller R degree than F; it need
not be R-free. No assumption that F is irreducible is needed for this argument.
The proof does not extend automatically to a projected or restricted kernel:
preservation of any extra linear constraints remains a separate obligation.

The derivative mechanism is already present in the companion as
`LocatorContact.locator_pderiv_contactAtLeast`, `pderiv_R_weight_add_le`,
`locator_pderiv_degreeR_le`, and `pderiv_R_ne_zero_of_degree_lt_char`
(`PackedLocatorTail.lean:648–757`, snapshot
`032154395c51fd6f77715a7f42d9a987ab9fb48a`). The new consequence assembles
these bounds with factor-specific locator exponents and same-kernel descent;
it is not a new differentiation identity.

## Agreement incidence through H

Let `H=∂RF`. For a selected polynomial f of degree at most w with seed γ,
assume `H(X,f,f',γ)` is nonzero, as required by regularity. At an agreement
node `f(x_i)=u0_i+γ u1_i`, substituting `R=f'(x_i+τ)` gives

```
v = f(x_i+τ)-f(x_i)-τ f'(x_i+τ),     ord_τ(v) ≥ 2.
```

Local contact order therefore gives a root of H's specialization of
multiplicity at least `max(0,ν_i-1)`. Distinct nodes contribute additively.
Its degree is at most `c-(w-1)`, because differentiating F in R lowers its
maximum contact weight by at least `w-1`. Consequently every regular selected
solution satisfies

```
Σ_{i agreeing with f} max(0,ν_i-1) ≤ c-(w-1).             (2)
```

This argument requires nonzero H specialization; it cannot be applied to the
identically zero specialization of F itself.

## Exact binding arithmetic and the remaining gap

For `w=131071, r=10`, (1) gives at least **131071 positive-contact nodes**,
improving the earlier 108076. It also gives
`Σ min(10,ν_i)≥1310701`, with the analogous thresholds for h=2 through 9.
These are necessary conditions, not a construction of a universal factor.

At the conservative exact-flag contact weight `c=6160327`, the previously
identified arithmetic profile `ν_i=34` at all 262144 nodes passes every one
of (1), the full-weight repair criterion, and the R-free interpolation test.
For a set of 181353 agreements, the left side of (2) is 5984649, below its
6029257 bound by 44608. Thus even this strengthened profile-and-incidence
system remains consistent. The uniform profile is not a constructed
polynomial or a received-word/family witness.

The nodes in (2) are vertical fibers in X. The C2 tail intersection is instead
computed on the generic surface over K(X), where every `X-x_i` is a unit.
Vertical vanishing alone therefore does not supply points or multiplicities
that can be subtracted from that generic intersection. A score improvement
still needs a theorem coupling the contact profile to the generic moving
divisor or to simultaneous selected-solution incidences. No such subtraction,
nor a proof that it is impossible, is established here.

Reproduce: `python3 scripts/probes/astra_incidence_derivative_repair.py`.
The probe checks the local derivative identity on 384 finite cases and the
displayed exact integer thresholds. The general inequalities rest on the
written proof above, rather than finite testing.

The [weighted secant follow-up](astra_family_incidence_secants-2026-09-04.md)
does supply a bridge from shared node contacts to lines on a non-plane
geometric component. Its resulting pair-incidence inequality still admits
the surviving uniform order-34 arithmetic profile.

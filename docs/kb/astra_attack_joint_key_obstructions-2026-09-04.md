# Companion attack: exact obstructions to simple joint-key savings

Date: 2026-09-04. Parameters are the actual companion values
`p=2130706433`, `F=256`, `r=136`; these are not toy-prime experiments.
The official upper construction is unchanged between inspected commits
`b34c0131cfa36b51111521541d7d3e35c8791082` and
`032154395c51fd6f77715a7f42d9a987ab9fb48a`.

The previous product-marginal calculation leaves a factor greater than four
missing from the pigeonhole guarantee. Two tempting ways to save key space
are a forced affine identity among the six top coefficients, or a proper
multiplicative-coset restriction on an extra evaluation key. Both fail at
the literal production prime, even inside the maximal product class `s=4`.
Neither result bounds nonlinear constraints or concentration of the joint map.

## Explicit seven-subset certificate

Let `z=392596362=3^((p-1)/256) mod p`, which has exact order 256, and let

```text
C = {3,4,6,7,...,136,165},  |C|=134,  sum C = 1 mod256,
U_0 = C union {1,2}.
```

Six more subsets are obtained from `U_0` by these pair exchanges:

| Removed | Inserted |
|---|---|
| `{1,2}` | `{5,254}` |
| `{1,3}` | `{5,255}` |
| `{1,18}` | `{137,138}` |
| `{1,19}` | `{137,139}` |
| `{1,20}` | `{137,140}` |
| `{1,21}` | `{137,141}` |

All seven subsets contain 136 labels, exclude zero, and sum to `4 mod256`.
Write `V_U(Y)=product_(j in U)(Y-z^j)`. For each subset compute its first
six elementary symmetric functions `E(U)`. The six-by-six matrix whose
rows are `E(U_i)-E(U_0)` has determinant

```text
626613800 mod p, which is nonzero.
```

The first six coefficients below the monic leading coefficient differ
from these functions only by alternating column signs, so their affine
span is also the full six-dimensional space. No nontrivial affine
identity can hold for those coefficients throughout this product fibre.

The same check in power-sum coordinates,
`P_j(U)=sum_(a in U)z^(aj)`, `j=1,...,6`, yields determinant

```text
1105802634 mod p, also nonzero.
```

This separately excludes an affine identity in the Newton power sums.
It does not assert that the coefficient image contains every possible
vector, nor that it is equidistributed.

## Extra-root evaluation values do not lie in a proper coset

One potential construction change replaces a top-coefficient condition
by equality of `V_U(1)`, obtaining an additional divisibility root. A
small multiplicative range for that evaluation could reduce its cost.

The first exchange above preserves the original product class but gives

```text
V_(U_0)(1) / V_(U_1)(1)
 = ((1-z)(1-z^2))/((1-z^5)(1-z^254))
 = 343834042 mod p.
```

This value has exact order `p-1=127*2^24`. The elementary order certificate is

```text
ratio^((p-1)/2)   = p-1,
ratio^((p-1)/127) = 359646889 != 1.
```

Both evaluations are nonzero because label zero is excluded. If all the
evaluation values in this product class lay in a coset `aH` of a proper
multiplicative subgroup, their ratios would lie in `H`. The displayed
primitive ratio makes that impossible.

This excludes a fixed proper-coset restriction. It does not prove that
all nonzero field values occur, that all occur equally often, or that
no other small image description exists.

## Reproduction and remaining opening

Run `python3 scripts/probes/astra_attack_joint_key_obstructions.py`.
The probe checks primality by exact trial division, generator order, every
subset and product label, and both determinants using independent
elimination and permutation-expansion algorithms. It also evaluates
the full products independently of the cancelled four-factor ratio.
The run passed on 2026-09-04.

No companion score improvement follows. A successful key-space saving
still could come from nonlinear relations or concentration of the six
coefficients within a product class, or from a different attack family.
No official submission files were changed and no Lean proof is claimed.

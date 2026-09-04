# Correlated ledger replay and the remaining 68.04 gap

The current official companion pin is
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a),
with score 68.03. Our two recorded 68.04 numerical candidates **fail the
combined counting budget**. A new generic Lean theorem validates the
simultaneous-source closure principle, but no concrete closure table,
polynomial bridge, or new `ProtocolClaim` has been certified.

## Exact arithmetic reproduction

[`astra_companion_joint_audit.py`](../../scripts/probes/astra_companion_joint_audit.py)
transcribes the new `ChainGroupMaj` formula. The correlated charge at raw
universal-child flag `(r,v,z)` is

```text
chainMaj(T, r, r+v)
+ chainMaj(T, 33-r, 153-v)
+ regularCount((153,max(1,33-r),LB), (YT,ST,LT))
+ chainMaj(LB,33-r,153)
+ 2*tailSingular
```

The second Y argument is **153 minus raw v**, not 153 minus `(r+v)`.
The greedy initial-A complement is added at the same flag. The outer fixed
tail charge is `34*tailH`; the scalar list count is added last.

The script matches all five upstream source nullities and all 15 source
potential coefficients, as well as the chain, residual, and tail literals.
It independently compares the closed-form majorant against the sum of the
individual regular-count floors in 20,944 cases. In every case the difference
is between zero and the maximum possible floor-rounding loss.

Our C++ implementation uses signed 128-bit arithmetic for counts and checks
source kernel positivity, support shape, and helper mixed degrees. The added
options are `--errors`, `--padding`, and `--joint`; existing modes retain their
previous behavior. These options are research arithmetic inputs, not proofs
that retuned algebraic assumptions hold.

## Numerical envelopes

The field-count capacity is `274980728111395087`. Counts below include the
correlated phase maximum, the fixed tails, and the scalar list count.

| Parameters and sources | Combined count | Capacity minus count |
|---|---:|---:|
| Official 68.03 parameters, five sources, our simultaneous closure | 271984204106331863 | 2996524005063224 |
| 68.04 kernels, six sources | 295260471698619242 | -20279743587224155 |
| 68.04 kernels, 29 sources | 293903315667449479 | -18922587556054392 |

The first row is a **research envelope evaluated at the official parameters**,
not a replay of the official sparse certificate. Our simultaneous closure
gives phase maximum `271913004621405880` at `(12,53,2534)`. The official
five-stage certified allowance is `273301903386687639`; our smaller numerical
value needs its own table certificate and polynomial integration.

At error cell 80791, the six-source envelope peaks at `(12,37,4371)` with
phase count `295186676786672598`. The denser ladder peaks at `(10,37,2331)`
with phase count `293829520755502835`. Its remaining excess is about 6.88%
of capacity. Merely adding these sources does not reach 68.04. This bounded
experiment establishes no impossibility or optimality result for other source
parameters or other counting arguments.

The six-source row adjusts multiplicity 8000 to 7999. At 80791, the original
8000 row violates `D+s <= w*(Y+1)` by 1565 despite positive interpolation
nullity. The evaluator correctly rejects it; positive nullity alone does not
establish a usable source.

## Kernel-checked closure principle

[`astra_companion_phase_closure.lean`](../../scripts/probes/astra_companion_phase_closure.lean)
proves two universal combinatorial statements with `Std` only:

1. Repeated strict source exits reach a nonrouteable child and preserve the
   additive charge balance.
2. If each source supplies those exits and a locally valid prefix certificate,
   taking the minimum across all sources with the **final child bound** is
   sound. Strong induction on raw slope resolves the apparent circularity.

This closes the general recursion argument behind the order-independent
`candidate-closure` mode. It does not certify the C++ implementation or supply
the concrete table inequalities. Both theorems were checked by Lean
4.30.0-rc2 and depend only on `propext` and `Quot.sound`.

The remaining proof obligations are the finite table certificate, the
connection to actual polynomial source splits, all retuned ordinary-factor
and kernel gates, and the final companion theorem under its pinned toolchain.
The full ArkLib build remains unavailable locally because Lake/Mathlib is not
installed; a successful standalone Std proof is not a full repository build.

## Reproduction

```sh
python3 scripts/probes/astra_companion_joint_audit.py
python3 scripts/probes/astra_companion_joint_audit.py --check-phases --reverse
python3 scripts/probes/astra_companion_joint_audit.py --sanitize
python3 scripts/probes/astra_companion_parameters.py --check-phases
lean scripts/probes/astra_companion_phase_closure.lean
```

The Python audit uses the standard library. Phase replay additionally needs a
C++17 compiler with signed 128-bit integer support. The dense replay uses
roughly 450 MB for the two prefix buffers. JSON output records every source,
the integer budget calculations, and whether phase replay ran in that invocation.

Validation passed for all three cases in forward and reverse source order,
all three UBSan replays, the four existing phase regressions, the standalone
Lean theorem, documentation links, and 11 malformed-option rejection cases.
The repository forbidden-token check passed with its nine existing allowlisted
residual axioms. The full repository gate then exited 127 at `lake: command
not found`; it did not produce a successful library build.

A fresh remote fetch at 2026-09-04 23:53 UTC found ArkLib main still at
`8e2fc19130e2fea9e175c52b0953b88804b8f333`, research at
`54007b004040a9cd0964dcb0a2413e86bc60ae8d`, and the official companion at the
68.03 pin above.

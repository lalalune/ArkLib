/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Std

/-!
# Exact arithmetic for three T-interpolant cutoff witnesses

These finite sums reproduce the coefficient and rectangular local-rank
formulas audited by `astra_t_audit.py`. The three inequalities use ordinary
kernel reduction. This file does not identify these definitions with the
official companion APIs, construct an interpolant, or prove a ProtocolClaim.
Source pin: proximity-prize/proximity-prize 032154395c51fd6f77715a7f42d9a987ab9fb48a.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace AstraCompanionTKernelGates

def sumBelow : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumBelow n f + f n

def rectangle (a b offset limit : Nat) : Nat :=
  a * b * (limit + 1 - offset) -
    (b * a * (a - 1) / 2 + a * b * (b - 1) / 2)

def localRank (m limit slope : Nat) : Nat :=
  sumBelow m fun r =>
    let degree := min r limit
    let contact := min (r + 1) (m - r)
    rectangle (degree + 1) (slope + 1) 0 limit -
      rectangle (degree + 1 - contact) (slope + 1 - contact) contact limit

def coefficientChannel (weighted limit j : Nat) : Nat :=
  let a := weighted - 131070 * j
  let b := limit + 1 - j
  if a = 0 ∨ b = 0 then 0 else
    let last := min (b - 1) ((a - 1) / 131071)
    let sumOne := last * (last + 1) / 2
    let sumTwo := last * (last + 1) * (2 * last + 1) / 6
    (last + 1) * a * b + 131071 * sumTwo - (a + b * 131071) * sumOne

def coefficients (weighted limit slope : Nat) : Nat :=
  sumBelow (slope + 1) (coefficientChannel weighted limit)

/-- The improved ledger row has positive quotient-kernel margin 108295388. -/
theorem row_166 :
    coefficients 30104598 7159 51 = 1014559635006775 ∧
    localRank 166 7159 51 = 3870236994 ∧
    coefficients 30104598 1 51 = 120156251 ∧
    coefficients 30104598 7159 51 =
      262144 * localRank 166 7159 51 + coefficients 30104598 1 51 + 108295388 := by
  decide

/-- Changing only the old row's cutoff also gives a positive margin. -/
theorem row_194 :
    coefficients 35182482 6923 60 = 1564018807121055 ∧
    localRank 194 6923 60 = 5966253535 ∧
    coefficients 35182482 4 60 = 1222211935 ∧
    coefficients 35182482 6923 60 =
      262144 * localRank 194 6923 60 + coefficients 35182482 4 60 + 18230080 := by
  decide

/-- The smallest selected total cap does not give the smallest final ledger. -/
theorem row_197 :
    coefficients 35726541 6922 61 = 1637984923333354 ∧
    localRank 197 6922 61 = 6248411181 ∧
    coefficients 35726541 4 61 = 1241254000 ∧
    coefficients 35726541 6922 61 =
      262144 * localRank 197 6922 61 + coefficients 35726541 4 61 + 181447290 := by
  decide

/-- Literal ambient embedding and selected-cap arithmetic for the three rows. -/
theorem ambient_and_cutoffs :
    30104598 = 166 * 181353 ∧ 30104598 + 51 ≤ 131071 * (229 + 1) ∧
    166 ≤ 270 ∧ 51 ≤ 81 ∧ 7159 ≤ 130000 ∧ 7159 = 7157 + 1 + 1 ∧
    35182482 = 194 * 181353 ∧ 35182482 + 60 ≤ 131071 * (268 + 1) ∧
    194 ≤ 270 ∧ 60 ≤ 81 ∧ 6923 ≤ 130000 ∧ 6923 = 6918 + 4 + 1 ∧
    35726541 = 197 * 181353 ∧ 35726541 + 61 ≤ 131071 * (272 + 1) ∧
    197 ≤ 270 ∧ 61 ≤ 81 ∧ 6922 ≤ 130000 ∧ 6922 = 6917 + 4 + 1 := by
  decide

#print axioms row_166
#print axioms row_194
#print axioms row_197
#print axioms ambient_and_cutoffs

end AstraCompanionTKernelGates

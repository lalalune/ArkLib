/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Std

/-!
# Exact widths of contact-band channels

For a fixed Y/R/Z channel of contact weight c, the x-exponents in the strip
`D-delta <= x+c < D` form an interval of length `min delta (D-c)`.
These universal natural-number theorems justify clipping a boundary channel
instead of charging delta for every channel in the thin box.

The final two lemmas locate the fully charged and possibly active cumulative
Y/R rows at the production weight 131071. This is arithmetic only: the
polynomial projection/rank bridge and the C++ fast-sum identity remain separate
obligations. No phase table or ProtocolClaim is certified here.
-/

set_option autoImplicit false

namespace AstraCompanionBandStrip

def width (D delta contact : Nat) : Nat := min delta (D-contact)
def start (D delta contact : Nat) : Nat := D-delta-contact

theorem width_eq_difference (D delta contact : Nat) :
    width D delta contact = (D-contact)-(D-delta-contact) := by
  unfold width
  omega

theorem start_add_width (D delta contact : Nat) :
    start D delta contact + width D delta contact = D-contact := by
  unfold start width
  omega

theorem channel_interval (D delta contact x : Nat) :
    (D-delta ≤ x+contact ∧ x+contact < D) ↔
      (start D delta contact ≤ x ∧ x < start D delta contact + width D delta contact) := by
  rw [start_add_width]
  unfold start
  omega

/-- Every valid channel exponent is represented by exactly one bounded index. -/
theorem channel_index (D delta contact x : Nat) :
    (D-delta ≤ x+contact ∧ x+contact < D) ↔
      ∃ i : Fin (width D delta contact), x = start D delta contact+i.val := by
  rw [channel_interval]
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨⟨x-start D delta contact, by omega⟩, ?_⟩
    change x = start D delta contact+(x-start D delta contact)
    omega
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    constructor <;> omega

theorem channel_index_injective (D delta contact : Nat)
    (i j : Fin (width D delta contact))
    (h : start D delta contact+i.val = start D delta contact+j.val) : i = j := by
  apply Fin.ext
  omega

theorem width_le_delta (D delta contact : Nat) : width D delta contact ≤ delta := by
  unfold width
  omega

theorem width_mono_high {D D' delta contact : Nat} (h : D ≤ D') :
    width D delta contact ≤ width D' delta contact := by
  unfold width
  omega

theorem width_antitone_contact {D delta contact contact' : Nat} (h : contact ≤ contact') :
    width D delta contact' ≤ width D delta contact := by
  unfold width
  omega

theorem width_zero (D delta contact : Nat) (h : D ≤ contact) :
    width D delta contact = 0 := by
  unfold width
  omega

/-- The original monomial has Y/R exponents (k-r,r), with r<=k.
The contact weight is 131071*k-r. -/
theorem active_row_le_thin_cut (D delta S k r : Nat)
    (hrk : r ≤ k) (hrS : r ≤ S)
    (hactive : 0 < width D delta (131071*k-r)) :
    k ≤ (D+S-1)/131071 := by
  unfold width at hactive
  omega

theorem full_row_width (D delta k r : Nat) (h : 131071*k+delta ≤ D) :
    width D delta (131071*k-r) = delta := by
  unfold width
  omega

def firstPartial (D delta : Nat) : Nat :=
  if delta ≤ D then (D-delta)/131071+1 else 0

/-- The fast strip evaluator visits at most two partial rows in its supported
range. This includes an empty high box and a strip wider than that box. -/
theorem at_most_two_partial_rows (D delta S : Nat) (h : delta+S ≤ 262142) :
    (D+S-1)/131071+1-firstPartial D delta ≤ 2 := by
  unfold firstPartial
  split <;> omega

#print axioms channel_index
#print axioms channel_index_injective
#print axioms active_row_le_thin_cut
#print axioms at_most_two_partial_rows

end AstraCompanionBandStrip

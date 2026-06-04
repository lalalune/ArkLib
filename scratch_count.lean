import Mathlib

open Finset

-- WALL CHARACTERIZATION for LD-counting. Reduction target = pure-Nat double-coverage.
-- EXPLICIT COUNTEREXAMPLE (m = 1, n = 2, ι = Fin 3, H = Fin 5):
-- every γ misses the SAME position 0 ∈ T (covering {1,2}); each misses exactly 1 = m;
-- |H| = 5 ≥ n+1 = 3; yet c₀ = 0 < 2.  Double-coverage of all of T is impossible for m ≥ 1.
example :
    (1 ≤ 1) ∧
    (2 + 1 ≤ (Finset.univ : Finset (Fin 5)).card) ∧
    ((0 : Fin 3) ∈ ({0, 1, 2} : Finset (Fin 3))) ∧
    (∀ γ ∈ (Finset.univ : Finset (Fin 5)),
        (((Finset.univ : Finset (Fin 3)) \ ({1, 2} : Finset (Fin 3)))
          ∩ ({0, 1, 2} : Finset (Fin 3))).card ≤ 1) ∧
    (((Finset.univ : Finset (Fin 5)).filter
        (fun _γ => (0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)))).card < 2) := by
  refine ⟨by norm_num, by decide, by decide, ?_, by decide⟩
  intro γ _; decide

import Std

/-!
Finite arithmetic certificate for an abstract C2 scalar-budget obstruction.
This constructs no polynomial, prime component, or local-DVR certificate.
-/

set_option autoImplicit false

namespace AstraC2BudgetObstruction

structure Flag where
  z : Nat
  v : Nat
  r : Nat

def mixed (p q t : Flag) : Nat :=
  (q.r * t.r + q.v * t.r + q.r * t.v) * (p.z + p.v + p.r) +
  (q.z * t.r + q.r * t.z) * (p.v + p.r) +
  (q.v * t.v + q.z * t.v + q.v * t.z) * p.r

def p : Flag := ⟨2317, 37, 10⟩
def tail : Flag := ⟨2 * 2317 * 131072, 1 + 2 * 37 * 131072, 18 * 131072⟩
def rational : Flag := ⟨131074 * 2317, 131074 * 36 + 2, 131074 * 8 + 3⟩
def fiber : Flag := ⟨2317, 37, 11⟩
def publishedCut : Flag := ⟨131074 * 2317, 131074 * 37, 131074 * 10 - 1⟩
def exactCut : Flag := ⟨131073 * 2317, 131073 * 37, 131073 * 10 - 1⟩
def zCap : Nat := mixed p tail ⟨1, 0, 0⟩
def yzCap : Nat := mixed p tail ⟨0, 1, 0⟩
def allCap : Nat := mixed p tail ⟨0, 0, 1⟩
def movingCap : Nat := mixed p fiber exactCut
def weighted (zC yzC allC : Nat) : Nat :=
  rational.z * zC + rational.v * yzC + rational.r * allC
def published : Nat := mixed p tail rational + 131076 * mixed p fiber publishedCut
def tightened : Nat := mixed p tail rational + 131076 * movingCap
def atom : Nat := weighted zCap yzCap allCap + 131072 * movingCap

theorem exact_values :
    published = 283403712362442072 ∧
    tightened = 283402911223701780 ∧
    atom = 283399706742974300 ∧
    weighted zCap yzCap allCap = mixed p tail rational := by decide

/-- The independent scalar caps do not entail a six-percent improvement,
even after removing the published moving-cut rounding and using multiplicity 1.
This is a counterexample to that finite scalar implication only. -/
theorem scalar_caps_do_not_imply_six_percent :
    ¬ (∀ zC yzC allC moving : Nat,
      zC ≤ zCap → yzC ≤ yzCap → allC ≤ allCap → moving ≤ movingCap →
      100 * (weighted zC yzC allC + 131072 * moving) ≤ 94 * published) := by
  intro h
  have hb := h zCap yzCap allCap movingCap
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  exact (by decide : ¬ (100 * atom ≤ 94 * published)) hb

#print axioms exact_values
#print axioms scalar_caps_do_not_imply_six_percent

end AstraC2BudgetObstruction

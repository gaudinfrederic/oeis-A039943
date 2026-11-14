import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! OEIS A039943 verbatim : "Every integer eventually goes to
    one of these under the 'x goes to sum of squares of digits
    of x' map". Data : 0, 1, 4, 16, 20, 37, 42, 58, 89, 145. -/

namespace A039943Spec

/-- The map of the entry : sum of the squares of the decimal
    digits (base 10, via Nat.digits). -/
def sqSum (n : ℕ) : ℕ := ((Nat.digits 10 n).map (· ^ 2)).sum

/-- The ten terms of the entry, in its order. -/
abbrev DATA : List ℕ := [0, 1, 4, 16, 20, 37, 42, 58, 89, 145]

end A039943Spec

open A039943Spec

/-- Enonce verbatim de la fiche : tout entier atteint l'un des
    dix termes. -/
abbrev SpecPropA039943 : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, (Nat.iterate sqSum k n) ∈ DATA

/-- Caracterisation exacte : les dix termes sont exactement les
    points periodiques de la fonction de la fiche. -/
abbrev SpecCharA039943 : Prop :=
  ∀ n : ℕ, n ∈ DATA ↔ ∃ p : ℕ, 1 ≤ p ∧ sqSum^[p] n = n

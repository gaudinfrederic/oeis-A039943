import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- OEIS A039943 verbatim : "Every integer eventually goes to one
    of these under the 'x goes to sum of squares of digits of x'
    map". Data : 0, 1, 4, 16, 20, 37, 42, 58, 89, 145. -/
abbrev SpecPropA039943 : Prop :=
  ∀ n : ℕ, ∃ k : ℕ,
    (Nat.iterate (fun m => ((Nat.digits 10 m).map (· ^ 2)).sum) k n) ∈
      [0, 1, 4, 16, 20, 37, 42, 58, 89, 145]

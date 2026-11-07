import Spec_A039943
import A039943

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Fermeture N0 : le theoreme prouve realise le spec verbatim. -/
theorem proven_spec_a039943 : SpecPropA039943 := by
  intro n
  obtain ⟨k, hk⟩ := A039943 n
  refine ⟨k, ?_⟩
  rw [iterateT_eq_nat] at hk
  exact hk

#print axioms A039943

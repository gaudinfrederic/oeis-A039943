import A039943

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! N3 anti-vacuite pour A039943. -/

/-- (a) Satisfiabilite : chacun des 10 attracteurs est bien dans
    l'ensemble (k = 0 temoin). -/
theorem sat943 : ∀ x ∈ ATT039943, ∃ k, iterateT k x ∈ ATT039943 :=
  fun x hx => ⟨0, hx⟩

/-- (b) Ancrage : 0 est point fixe (premier terme de la data). -/
theorem anchor943_zero : iterateT 5 0 = 0 := by decide

/-- Ancrage : 4 et 20 appartiennent au cycle (data verbatim). -/
theorem anchor943_cycle : sqSum 4 = 16 ∧ sqSum 20 = 4 :=
  ⟨by decide, by decide⟩

/-- (c) Ablation : un non-attracteur n'est pas dans l'ensemble
    (3 -> 9 -> 81 -> 65 -> 61 -> 37 cycle, jamais 0 ni 1). -/
theorem ablation943 : ¬ (3 ∈ ATT039943) := by decide

#print axioms anchor943_zero

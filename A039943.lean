import A007770

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A039943 - attracteurs de la map "somme des carres des chiffres"

OEIS A039943 verbatim : "Every integer eventually goes to one of
these under the 'x goes to sum of squares of digits of x' map".
Data : 0, 1, 4, 16, 20, 37, 42, 58, 89, 145 (fini, full).

THEOREME (corollaire direct d'A007770/reaches_S) :
  tout n atteint l'ensemble d'attracteurs
  {0, 1, 4, 16, 20, 37, 42, 58, 89, 145}
  (0 = point fixe, 1 = happy, le 8-cycle sinon).
-/

/-- L'ensemble d'attracteurs OEIS (verbatim, ordre de la fiche). -/
def ATT039943 : List ℕ := [0, 1, 4, 16, 20, 37, 42, 58, 89, 145]

/-- Le 8-cycle de CYC770 est inclus dans l'ensemble verbatim. -/
theorem cyc770_sub_att (x : ℕ) (hx : x ∈ CYC770) :
    x ∈ ATT039943 := by
  unfold CYC770 at hx
  unfold ATT039943
  fin_cases hx <;> decide

/-- Theoreme principal : toute orbite atteint l'un des 10
    attracteurs (reponse exacte a la fiche A039943). -/
theorem A039943 (n : ℕ) :
    ∃ k, iterateT k n ∈ ATT039943 := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨0, by decide⟩
  · obtain ⟨k, hk⟩ := reaches_S n hn
    refine ⟨k, ?_⟩
    rcases hk with h1 | hc
    · rw [h1]; decide
    · exact cyc770_sub_att _ hc

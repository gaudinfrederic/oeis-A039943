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

/-- Stabilite : `sqSum` envoie l'ensemble verbatim dans
    lui-meme (decide sur les 10 elements). -/
theorem att039943_stable (x : ℕ) (hx : x ∈ ATT039943) :
    sqSum x ∈ ATT039943 := by
  unfold ATT039943 at *
  fin_cases hx <;> decide

/-- Iterer a partir d'un element de ATT reste dans ATT. -/
theorem att039943_iterate_mem {x : ℕ} (hx : x ∈ ATT039943) :
    ∀ k, Nat.iterate sqSum k x ∈ ATT039943 := by
  intro k; induction k generalizing x with
  | zero => exact hx
  | succ k ih => exact ih (att039943_stable x hx)

/-- Periodicite : chaque element de ATT039943 est periodique,
    uniformement de periode 8 (0 et 1 sont deja fixes). -/
theorem att039943_mem_periodic (x : ℕ) (hx : x ∈ ATT039943) :
    ∃ p, 1 ≤ p ∧ Nat.iterate sqSum p x = x :=
  ⟨8, by norm_num, by
    unfold ATT039943 at hx
    fin_cases hx <;> decide⟩

/-- Decomposition des iteres : `sqSum` applique `a + b` fois. -/
theorem sqSum_iterate_add (a b : ℕ) (x : ℕ) :
    Nat.iterate sqSum (a + b) x =
      Nat.iterate sqSum a (Nat.iterate sqSum b x) := by
  induction b generalizing x with
  | zero => rfl
  | succ b ih => exact ih (sqSum x)

/-- Un point de periode `p` a aussi periode `m * p`. -/
theorem sqSum_iterate_mul {p x : ℕ}
    (h : Nat.iterate sqSum p x = x) :
    ∀ m, Nat.iterate sqSum (m * p) x = x := by
  intro m; induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, sqSum_iterate_add, h]; exact ih

/-- Tout point periodique de `sqSum` appartient a ATT039943 :
    l'orbite atteint ATT (A039943) et y reste (stabilite), et la
    periodicite ramene n dans ce segment. -/
theorem att039943_of_periodic {n : ℕ} {p : ℕ} (hp : 1 ≤ p)
    (hfix : Nat.iterate sqSum p n = n) : n ∈ ATT039943 := by
  obtain ⟨k, hk⟩ := A039943 n
  rw [iterateT_eq_nat] at hk
  have hkp : Nat.iterate sqSum (k * p) n = n :=
    sqSum_iterate_mul hfix k
  have hge : k ≤ k * p := by
    have h := Nat.mul_le_mul_left k hp
    rwa [Nat.mul_one] at h
  have hd : k * p - k + k = k * p := Nat.sub_add_cancel hge
  rw [← hd, sqSum_iterate_add] at hkp
  have hin := att039943_iterate_mem hk (k * p - k)
  rwa [hkp] at hin

/-- Caracterisation exacte : les points periodiques de `sqSum`
    sont exactement les 10 elements de la fiche (revue OEIS :
    la liste verbatim ne contient ni intrus ni manquant). -/
theorem att039943_iff_periodic (n : ℕ) :
    n ∈ ATT039943 ↔ ∃ p, 1 ≤ p ∧ Nat.iterate sqSum p n = n :=
  ⟨att039943_mem_periodic n, fun ⟨_p, hp, h⟩ =>
    att039943_of_periodic hp h⟩

/-- Toute orbite reste definitivement piegee dans ATT039943. -/
theorem att039943_eventually (n : ℕ) :
    ∃ K, ∀ k, K ≤ k → Nat.iterate sqSum k n ∈ ATT039943 := by
  obtain ⟨K, hK⟩ := A039943 n
  rw [iterateT_eq_nat] at hK
  refine ⟨K, fun k hk => ?_⟩
  have hkd : k = k - K + K := (Nat.sub_add_cancel hk).symm
  rw [hkd, sqSum_iterate_add]
  exact att039943_iterate_mem hK (k - K)

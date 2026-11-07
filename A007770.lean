import A007770Defs
import A007770Cert

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-!
# A007770 — nombres heureux (happy numbers)

OEIS A007770 : "Happy numbers: numbers whose trajectory under
iteration of sum of squares of digits map includes 1."

THEOREME (dichotomie des attracteurs, kernel-pur) :
  tout n ≥ 1 atteint soit 1 (happy), soit le 8-cycle
  {4,16,37,58,89,145,42,20} :
  `∃ k, iterateT k n = 1 ∨ iterateT k n ∈ CYC770`

Couvre aussi le contenu d'A039943 (meme attracteur).

Structure :
- `sqSum_bound` : n ≥ 1000 => sqSum n < n (81·L < 10^(L-1)).
- `cert_descent770` : sqSum n < n pour n ∈ [100,999] (decide).
- `cert_orbits770` : tout n ∈ [1,99] atteint S en ≤ 30 pas.
- `reaches_S` : induction forte sur n (sqSum n < n => IH).
-/

/-- Le 8-cycle non trivial de la somme des carres des chiffres. -/
def CYC770 : List ℕ := [4, 16, 37, 58, 89, 145, 42, 20]

/-- Pont Bool → Prop pour inS. -/
theorem inS_true {n : ℕ} (h : inS n = true) :
    n = 1 ∨ n ∈ CYC770 := by
  unfold inS at h
  have hm := (List.contains_iff_mem).mp h
  unfold CYC770
  rcases List.mem_cons.mp hm with h1 | h2
  · exact Or.inl h1
  · exact Or.inr h2

/-- Pont certificat → Prop : reachesS fuel n = true implique
    l'existence d'un pas k atteignant S. -/
theorem reachesS_true (fuel n : ℕ) (h : reachesS fuel n = true) :
    ∃ k, iterateT k n = 1 ∨ iterateT k n ∈ CYC770 := by
  induction fuel generalizing n with
  | zero => simp [reachesS] at h
  | succ f ih =>
      unfold reachesS at h
      rw [Bool.or_eq_true] at h
      rcases h with hinS | hrec
      · exact ⟨0, inS_true hinS⟩
      · obtain ⟨k, hk⟩ := ih _ hrec
        exact ⟨k + 1, hk⟩

/-- n ≥ 1000 => len(digits) ≥ 4. -/
theorem len_ge_four (n : ℕ) (hn : 1000 ≤ n) :
    3 < (Nat.digits 10 n).length := by
  by_contra hc
  push_neg at hc
  have h1 := Nat.lt_base_pow_length_digits (b := 10) (m := n)
    (by norm_num)
  have h2 : n < 10 ^ 3 :=
    lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hc)
  omega

/-- Tout n ≥ 1 atteint 1 ou le 8-cycle (dichotomie A007770). -/
theorem reaches_S (n : ℕ) : n ≠ 0 →
    ∃ k, iterateT k n = 1 ∨ iterateT k n ∈ CYC770 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h100 : n < 100
    · have hmem : n ∈ List.range' 1 99 := by
        rw [List.mem_range']
        exact ⟨n - 1, by omega, by omega⟩
      exact reachesS_true 30 n
        (List.all_eq_true.mp cert_orbits770 n hmem)
    · have hdesc : sqSum n < n := by
        by_cases h1000 : n < 1000
        · have hmem : n - 100 ∈ List.range 900 := by
            rw [List.mem_range]
            omega
          have hck := List.all_eq_true.mp cert_descent770
            (n - 100) hmem
          have hlt : sqSum (n - 100 + 100) < n - 100 + 100 :=
            of_decide_eq_true hck
          rw [Nat.sub_add_cancel (by omega : 100 ≤ n)] at hlt
          exact hlt
        · exact sqSum_bound n (len_ge_four n (by omega))
      have hpos : sqSum n ≠ 0 := Nat.ne_of_gt (sqSum_pos n hn)
      obtain ⟨k, hk⟩ := ih (sqSum n) hdesc hpos
      exact ⟨k + 1, hk⟩

/-- Pont avec Nat.iterate (spec verbatim). Nat.iterate =
    Function.iterate : application front, meme recursion
    qu'iterateT - defeq direct. -/
theorem iterateT_eq_nat (k n : ℕ) :
    iterateT k n = Nat.iterate sqSum k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => exact ih (sqSum n)

/-- Theoreme principal : dichotomie des orbites de la somme des
    carres des chiffres (contenu dynamique d'A007770/A039943). -/
theorem A007770 (n : ℕ) (hn : n ≠ 0) :
    ∃ k, iterateT k n = 1 ∨ iterateT k n ∈ CYC770 :=
  reaches_S n hn

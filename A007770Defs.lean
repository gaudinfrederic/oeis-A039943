import Mathlib
import A046253Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-- OEIS A007770 : "Happy numbers" - somme des carres des chiffres.
    Orbite atteint 1 (happy) ou le 8-cycle
    {4,16,37,58,89,145,42,20} (attracteur unique non trivial). -/
def sqSum (n : ℕ) : ℕ := ((Nat.digits 10 n).map (· ^ 2)).sum

/-- Iteration de sqSum, k fois. -/
def iterateT : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => iterateT k (sqSum n)

/-- Le 8-cycle non trivial + le point fixe 1. -/
def inS (n : ℕ) : Bool :=
  (1 :: [4, 16, 37, 58, 89, 145, 42, 20]).contains n

/-- Certificat : atteint S en au plus `fuel` pas. -/
def reachesS : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, n => inS n || reachesS fuel (sqSum n)

/-- Chaque chiffre au carre ≤ 81. -/
theorem sq_le_81 {d : ℕ} (hd : d < 10) : d ^ 2 ≤ 81 := by
  interval_cases d <;> decide

/-- sqSum n ≤ 81 * (nombre de chiffres). -/
theorem sqSum_le (n : ℕ) :
    sqSum n ≤ 81 * (Nat.digits 10 n).length := by
  unfold sqSum
  have hb : ∀ x ∈ (Nat.digits 10 n).map (· ^ 2), x ≤ 81 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    exact sq_le_81 (Nat.digits_lt_base (b := 10) (m := n)
      (by norm_num) hd)
  calc ((Nat.digits 10 n).map (· ^ 2)).sum
      ≤ ((Nat.digits 10 n).map (· ^ 2)).length * 81 :=
        List.sum_le_length_nsmul _ _ hb
    _ = (Nat.digits 10 n).length * 81 := by rw [List.length_map]
    _ = 81 * (Nat.digits 10 n).length := by rw [Nat.mul_comm]

/-- Clef de la borne : 81·(k+4) < 10^(k+3) pour tout k.
    Base : 81·4 = 324 < 1000. -/
theorem bound_key770 (k : ℕ) : 81 * (k + 4) < 10 ^ (k + 3) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : (10 : ℕ) ^ (k + 1 + 3) = 10 * 10 ^ (k + 3) := by ring
      have hlin : 81 * (k + 1 + 4) = 81 * (k + 4) + 81 := by ring
      have h81 : 81 ≤ (10 : ℕ) ^ (k + 3) := by
        have hb : (10 : ℕ) ^ 3 ≤ 10 ^ (k + 3) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 3 k)
        norm_num at hb ⊢
        omega
      have ha : 0 < (10 : ℕ) ^ (k + 3) := by positivity
      omega

/-- Borne de finitude : a `L > 3` chiffres (n ≥ 1000),
    sqSum n < n. -/
theorem sqSum_bound (n : ℕ)
    (h : 3 < (Nat.digits 10 n).length) :
    sqSum n < n := by
  have hn : n ≠ 0 := by
    intro h0
    rw [h0, Nat.digits_zero] at h
    simp at h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  have hL : (Nat.digits 10 n).length = k + 4 := by omega
  have hbase : 10 ^ (Nat.digits 10 n).length ≤ 10 * n :=
    Nat.base_pow_length_digits_le 10 n (by norm_num) hn
  rw [hL] at hbase
  have hprev : 10 ^ (k + 3) ≤ n := by
    have hp : (10 : ℕ) ^ (k + 4) = 10 * 10 ^ (k + 3) := by ring
    rw [hp] at hbase
    exact Nat.le_of_mul_le_mul_left hbase (by norm_num)
  have h2 := sqSum_le n
  rw [hL] at h2
  have hk2 := bound_key770 k
  omega

/-- sqSum d'un nombre ≥ 1 est ≥ 1 (le chiffre de tete est ≠ 0). -/
theorem sqSum_pos (n : ℕ) (hn : n ≠ 0) : 1 ≤ sqSum n := by
  unfold sqSum
  have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hz : (Nat.digits 10 n).getLast hne ≠ 0 :=
    Nat.getLast_digit_ne_zero 10 hn
  have hmem : (Nat.digits 10 n).getLast hne ∈ Nat.digits 10 n :=
    List.getLast_mem hne
  have hsq : ((Nat.digits 10 n).getLast hne) ^ 2 ∈
      (Nat.digits 10 n).map (· ^ 2) := List.mem_map_of_mem hmem
  have hpos : 1 ≤ ((Nat.digits 10 n).getLast hne) ^ 2 := by
    have h1 : 1 ≤ (Nat.digits 10 n).getLast hne := by omega
    nlinarith [h1]
  have hle := List.single_le_sum (fun x _ => Nat.zero_le x) _ hsq
  omega

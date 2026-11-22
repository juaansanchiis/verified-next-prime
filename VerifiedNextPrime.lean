import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import ShortIntervalPrimes

namespace VerifiedNextPrime

/-- Cota entera 100% computable que domina estrictamente a √x · ln x para todo x ≥ 4. -/
def searchBound (x : ℕ) : ℕ :=
  (Nat.sqrt x + 1) * (Nat.log2 x + 1)

/-- Escáner determinista ejecutable: busca el primer primo en [k, k + fuel). -/
def scanPrime (k : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
      if Nat.Prime k then some k
      else scanPrime (k + 1) fuel

lemma scanPrime_sound {k fuel p : ℕ} (h : scanPrime k fuel = some p) :
    Nat.Prime p ∧ k ≤ p ∧ p < k + fuel := by
  induction fuel generalizing k with
  | zero => simp [scanPrime] at h
  | succ f ih =>
    unfold scanPrime at h
    split_ifs at h with hp
    · injection h with hEq
      subst hEq
      exact ⟨hp, le_rfl, by omega⟩
    · rcases ih h with ⟨hp', hle, hlt⟩
      exact ⟨hp', by omega, by omega⟩

lemma scanPrime_isSome_of_exists {k fuel : ℕ}
    (hex : ∃ p, Nat.Prime p ∧ k ≤ p ∧ p < k + fuel) :
    (scanPrime k fuel).isSome := by
  induction fuel generalizing k with
  | zero =>
    rcases hex with ⟨p, _, hle, hlt⟩
    omega
  | succ f ih =>
    unfold scanPrime
    split_ifs with hp
    · rfl
    · apply ih
      rcases hex with ⟨p, hp', hle, hlt⟩
      have hne : k ≠ p := fun hEq => hp (hEq ▸ hp')
      exact ⟨p, hp', by omega, by omega⟩

lemma real_bound_lt_searchBound {x : ℕ} (hx : 4 ≤ x) :
    Real.sqrt (x : ℝ) * Real.log (x : ℝ) < (searchBound x : ℝ) := by
  unfold searchBound
  have hx0 : (0 : ℝ) < x := by positivity
  have hsqrt : Real.sqrt (x : ℝ) < ((Nat.sqrt x + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_lt' (by positivity)]
    have hlt : x < (Nat.sqrt x + 1) * (Nat.sqrt x + 1) := Nat.lt_succ_sqrt x
    have hcast : (x : ℝ) < ((Nat.sqrt x + 1 : ℕ) : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast hlt
    exact hcast
  have hlog : Real.log (x : ℝ) < ((Nat.log2 x + 1 : ℕ) : ℝ) := by
    have h2 : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
    have hcast : (x : ℝ) < (2 : ℝ) ^ (Nat.log2 x + 1) := by exact_mod_cast h2
    have hln : Real.log (x : ℝ) < ((Nat.log2 x + 1 : ℕ) : ℝ) * Real.log 2 := by
      have := Real.log_lt_log hx0 hcast
      rwa [Real.log_pow] at this
    have hln2 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [Real.exp_one_gt_d9]
    nlinarith [show (0 : ℝ) < ((Nat.log2 x + 1 : ℕ) : ℝ) by positivity]
  rw [Nat.cast_mul]
  exact mul_lt_mul'' hsqrt hlog (Real.sqrt_nonneg _)
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x)))

lemma scanPrime_always_succeeds
    (hRH : RiemannHypothesis) {x : ℕ} (hx : 4 ≤ x) :
    (scanPrime (x + 1) (searchBound x)).isSome := by
  apply scanPrime_isSome_of_exists
  have hxR : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  rcases ShortIntervalPrimes.exists_prime_in_short_interval hRH hxR with ⟨p, hp, hgt, hle⟩
  have hB := real_bound_lt_searchBound hx
  refine ⟨p, hp, ?_, ?_⟩
  · have : x < p := by exact_mod_cast hgt
    omega
  · have hltR : (p : ℝ) < ((x + searchBound x : ℕ) : ℝ) := by
      push_cast; linarith
    have hltN : p < x + searchBound x := by exact_mod_cast hltR
    omega

def nextPrimeDet (hRH : RiemannHypothesis) (x : ℕ) (hx : 4 ≤ x) : ℕ :=
  (scanPrime (x + 1) (searchBound x)).get (scanPrime_always_succeeds hRH hx)

theorem nextPrimeDet_isPrime (hRH : RiemannHypothesis) (x : ℕ) (hx : 4 ≤ x) :
    Nat.Prime (nextPrimeDet hRH x hx) := by
  have h := Option.some_get (scanPrime_always_succeeds hRH hx)
  exact (scanPrime_sound h.symm).1

theorem nextPrimeDet_gt (hRH : RiemannHypothesis) (x : ℕ) (hx : 4 ≤ x) :
    x < nextPrimeDet hRH x hx := by
  unfold nextPrimeDet
  have h := Option.some_get (scanPrime_always_succeeds hRH hx)
  have hge := (scanPrime_sound h.symm).2.1
  omega

theorem nextPrimeDet_le_bound (hRH : RiemannHypothesis) (x : ℕ) (hx : 4 ≤ x) :
    nextPrimeDet hRH x hx ≤ x + searchBound x := by
  unfold nextPrimeDet
  have h := Option.some_get (scanPrime_always_succeeds hRH hx)
  have hlt := (scanPrime_sound h.symm).2.2
  omega

end VerifiedNextPrime

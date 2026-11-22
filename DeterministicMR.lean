import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ShortIntervalPrimes
import VerifiedNextPrime

namespace DeterministicMR

/-- Exponenciación modular rápida: a^e mod m en O(log e). -/
def powMod (a e m : ℕ) : ℕ :=
  if m ≤ 1 then 0
  else if e = 0 then 1
  else
    let half := powMod a (e / 2) m
    let sq := (half * half) % m
    if e % 2 == 1 then (sq * (a % m)) % m else sq
termination_by e

/-- Descompone n = 2^s * d con d impar. -/
def splitTwos (n : ℕ) : ℕ × ℕ :=
  if n = 0 then (0, 0)
  else if n % 2 == 0 then
    let (s, d) := splitTwos (n / 2)
    (s + 1, d)
  else (0, n)
termination_by n

/-- Eleva al cuadrado hasta `steps` veces buscando x ≡ n - 1 (mod n). -/
def checkSquares (x n : ℕ) : ℕ → Bool
  | 0 => false
  | steps + 1 =>
      let next := (x * x) % n
      if next == n - 1 then true
      else checkSquares next n steps

/-- Test de pseudoprimo fuerte (Miller-Rabin) para una base `a`. -/
def isStrongPRP (n a : ℕ) : Bool :=
  let (s, d) := splitTwos (n - 1)
  let x := powMod a d n
  if x == 1 || x == n - 1 then true
  else checkSquares x n (s - 1)

/-- Cota entera computable que domina a 2 * (ln n)^2. -/
def bachBound (n : ℕ) : ℕ :=
  min (n - 1) (2 * (Nat.log2 n + 1) ^ 2)

/-- Comprueba `isStrongPRP n a` para todas las bases `a` en [lo, hi]. -/
def checkBases (n lo hi : ℕ) : Bool :=
  if hi < lo then true
  else if isStrongPRP n lo then checkBases n (lo + 1) hi
  else false
termination_by hi + 1 - lo

/-- Test de primalidad determinista de Miller-Rabin (O(log^4 n)). -/
def isPrimeMR (n : ℕ) : Bool :=
  if n < 2 then false
  else if n == 2 || n == 3 then true
  else if n % 2 == 0 then false
  else checkBases n 2 (bachBound n)

/-! ### Completitud de Miller-Rabin: todo primo pasa `isPrimeMR` (sin `sorry`) -/

lemma powMod_eq (a e m : ℕ) (hm : 1 < m) : powMod a e m = a ^ e % m := by
  induction e using Nat.strong_induction_on with
  | ind e ih =>
    unfold powMod
    have hnotle : ¬ m ≤ 1 := by omega
    rw [if_neg hnotle]
    by_cases he : e = 0
    · subst he
      simp [Nat.mod_eq_of_lt hm]
    · rw [if_neg he]
      have hhalf : powMod a (e / 2) m = a ^ (e / 2) % m := ih (e / 2) (by omega)
      simp only [hhalf]
      have hsq : a ^ (e / 2) % m * (a ^ (e / 2) % m) % m = a ^ (2 * (e / 2)) % m := by
        rw [← Nat.mul_mod, ← pow_add, two_mul]
      rw [hsq]
      by_cases hodd : e % 2 = 1
      · simp only [hodd, beq_self_eq_true, ↓reduceIte]
        rw [← Nat.mul_mod, ← pow_succ]
        congr 2
        omega
      · have heven : (e % 2 == 1) = false := by
          simp [beq_eq_false_iff_ne, hodd]
        simp only [heven, Bool.false_eq_true, ↓reduceIte]
        congr 2
        omega

lemma splitTwos_spec : ∀ n : ℕ, 0 < n →
    2 ^ (splitTwos n).1 * (splitTwos n).2 = n ∧ (splitTwos n).2 % 2 = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    unfold splitTwos
    have hne : n ≠ 0 := by omega
    rw [if_neg hne]
    by_cases heven : n % 2 = 0
    · simp only [heven, beq_self_eq_true, ↓reduceIte]
      have hhalf_pos : 0 < n / 2 := by omega
      rcases ih (n / 2) (by omega) hhalf_pos with ⟨heq, hodd⟩
      refine ⟨?_, hodd⟩
      calc 2 ^ ((splitTwos (n / 2)).1 + 1) * (splitTwos (n / 2)).2
          = 2 * (2 ^ (splitTwos (n / 2)).1 * (splitTwos (n / 2)).2) := by ring
        _ = 2 * (n / 2) := by rw [heq]
        _ = n := by omega
    · have hfalse : (n % 2 == 0) = false := by
        simp [beq_eq_false_iff_ne, heven]
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by simp, by omega⟩

lemma splitTwos_fst_pos {n : ℕ} (hn : 0 < n) (heven : n % 2 = 0) :
    1 ≤ (splitTwos n).1 := by
  unfold splitTwos
  have hne : n ≠ 0 := by omega
  rw [if_neg hne]
  simp only [heven, beq_self_eq_true, ↓reduceIte]
  omega

lemma natCast_eq_neg_one_iff_eq_sub_one {p x : ℕ} (hp : 1 < p) (hx : x < p) :
    (x : ZMod p) = -1 ↔ x = p - 1 := by
  have hsub : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, zero_sub, Nat.cast_one]
  rw [← hsub, ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    rw [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega : p - 1 < p)] at h
    exact h
  · intro h
    rw [h]

lemma natCast_eq_one_iff_eq_one {p x : ℕ} (hp : 1 < p) (hx : x < p) :
    (x : ZMod p) = 1 ↔ x = 1 := by
  rw [← Nat.cast_one (R := ZMod p), ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    rw [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hp] at h
    exact h
  · intro h
    rw [h]

lemma checkSquares_eq_true_of_pow_eq_one {p : ℕ} [Fact p.Prime] (steps : ℕ) :
    ∀ x : ℕ,
      (x : ZMod p) ≠ 1 →
      (x : ZMod p) ≠ -1 →
      (x : ZMod p) ^ (2 ^ (steps + 1)) = 1 →
      checkSquares x p steps = true := by
  have hp : p.Prime := Fact.out
  induction steps with
  | zero =>
    intro x hne1 hnem1 hpow
    simp only [zero_add, pow_one] at hpow
    rcases sq_eq_one_iff.mp hpow with h1 | hm1
    · exact absurd h1 hne1
    · exact absurd hm1 hnem1
  | succ m ih =>
    intro x hne1 hnem1 hpow
    unfold checkSquares
    set next := (x * x) % p
    by_cases hnext : next = p - 1
    · simp [hnext]
    · have hfalse : (next == p - 1) = false := by
        simp [beq_eq_false_iff_ne, hnext]
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      have hnext_cast : (next : ZMod p) = (x : ZMod p) ^ 2 := by
        dsimp [next]
        rw [ZMod.natCast_mod, Nat.cast_mul, sq]
      have hnext_lt : next < p := Nat.mod_lt _ hp.pos
      have hnext_ne_m1 : (next : ZMod p) ≠ -1 := by
        intro hm1
        exact hnext ((natCast_eq_neg_one_iff_eq_sub_one hp.one_lt hnext_lt).mp hm1)
      have hnext_ne_1 : (next : ZMod p) ≠ 1 := by
        intro h1
        rw [hnext_cast] at h1
        rcases sq_eq_one_iff.mp h1 with hx1 | hxm1
        · exact hne1 hx1
        · exact hnem1 hxm1
      have hnext_pow : (next : ZMod p) ^ (2 ^ (m + 1)) = 1 := by
        rw [hnext_cast, ← pow_mul]
        have hexp : 2 * 2 ^ (m + 1) = 2 ^ (m + 2) := by ring
        rw [hexp]
        exact hpow
      exact ih next hnext_ne_1 hnext_ne_m1 hnext_pow

lemma isStrongPRP_of_prime {p a : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p)
    (ha1 : 1 ≤ a) (hap : a < p) : isStrongPRP p a = true := by
  have : Fact p.Prime := ⟨hp⟩
  unfold isStrongPRP
  have hp1_pos : 0 < p - 1 := by omega
  have hp1_even : (p - 1) % 2 = 0 := by
    have hodd := hp.eq_two_or_odd
    omega
  rcases splitTwos_spec (p - 1) hp1_pos with ⟨hsd, _⟩
  have hs1 : 1 ≤ (splitTwos (p - 1)).1 := splitTwos_fst_pos hp1_pos hp1_even
  set s := (splitTwos (p - 1)).1
  set d := (splitTwos (p - 1)).2
  set x := powMod a d p
  change (if (x == 1 || x == p - 1) = true then true else checkSquares x p (s - 1)) = true
  have hx_eq : x = a ^ d % p := powMod_eq a d p hp.one_lt
  have hx_lt : x < p := by rw [hx_eq]; exact Nat.mod_lt _ hp.pos
  by_cases h1 : x = 1 ∨ x = p - 1
  · rcases h1 with hx1 | hxm1
    · simp [hx1]
    · simp [hxm1]
  · push Not at h1
    have hcond : ((x == 1) || (x == p - 1)) = false := by
      simp [beq_eq_false_iff_ne, h1.1, h1.2]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    have hx_ne_1 : (x : ZMod p) ≠ 1 :=
      fun h => h1.1 ((natCast_eq_one_iff_eq_one hp.one_lt hx_lt).mp h)
    have hx_ne_m1 : (x : ZMod p) ≠ -1 :=
      fun h => h1.2 ((natCast_eq_neg_one_iff_eq_sub_one hp.one_lt hx_lt).mp h)
    have ha_ne_0 : (a : ZMod p) ≠ 0 := by
      intro h0
      have hdvd : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp h0
      have hle : p ≤ a := Nat.le_of_dvd (by omega) hdvd
      omega
    have hx_pow : (x : ZMod p) ^ (2 ^ (s - 1 + 1)) = 1 := by
      have hs_eq : s - 1 + 1 = s := by omega
      rw [hs_eq, hx_eq, ZMod.natCast_mod, Nat.cast_pow, ← pow_mul, mul_comm d, hsd]
      exact ZMod.pow_card_sub_one_eq_one ha_ne_0
    exact checkSquares_eq_true_of_pow_eq_one (s - 1) x hx_ne_1 hx_ne_m1 hx_pow

lemma checkBases_of_forall {n : ℕ} :
    ∀ lo hi : ℕ, (∀ a, lo ≤ a → a ≤ hi → isStrongPRP n a = true) →
      checkBases n lo hi = true := by
  intro lo hi
  induction hlen : hi + 1 - lo generalizing lo with
  | zero =>
    intro _
    unfold checkBases
    have hlt : hi < lo := by omega
    rw [if_pos hlt]
  | succ k ih =>
    intro hall
    unfold checkBases
    have hnotlt : ¬ hi < lo := by omega
    rw [if_neg hnotlt]
    have hlo : isStrongPRP n lo = true := hall lo le_rfl (by omega)
    rw [if_pos hlo]
    exact ih (lo + 1) (by omega) (fun a ha1 ha2 => hall a (by omega) ha2)

/-- Completitud de Miller-Rabin: todo primo pasa `isPrimeMR`. -/
theorem isPrimeMR_of_prime {n : ℕ} (hn : Nat.Prime n) : isPrimeMR n = true := by
  unfold isPrimeMR
  have hnotlt2 : ¬ n < 2 := by have := hn.two_le; omega
  rw [if_neg hnotlt2]
  by_cases h23 : n = 2 ∨ n = 3
  · rcases h23 with rfl | rfl <;> simp
  · push Not at h23
    have hcond : ((n == 2) || (n == 3)) = false := by
      simp [beq_eq_false_iff_ne, h23.1, h23.2]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    have hodd : (n % 2 == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      have := hn.eq_two_or_odd
      omega
    simp only [hodd, Bool.false_eq_true, ↓reduceIte]
    apply checkBases_of_forall
    intro a ha1 ha2
    have hbach : bachBound n ≤ n - 1 := Nat.min_le_left _ _
    exact isStrongPRP_of_prime hn (by omega) (by omega) (by omega)

/-! ### Parte algebraica de Miller-Rabin: subgrupo propio y carácter de Dirichlet (sin `sorry`) -/

lemma checkSquares_sound {n : ℕ} (hn : 1 < n) :
    ∀ (steps x : ℕ), checkSquares x n steps = true →
      ∃ j < steps, ((x : ZMod n) ^ (2 ^ (j + 1))) = -1 := by
  intro steps
  induction steps with
  | zero =>
    intro x h
    simp [checkSquares] at h
  | succ m ih =>
    intro x h
    unfold checkSquares at h
    set next := (x * x) % n
    have hnext_cast : (next : ZMod n) = (x : ZMod n) ^ 2 := by
      dsimp [next]
      rw [ZMod.natCast_mod, Nat.cast_mul, sq]
    by_cases hhit : next = n - 1
    · refine ⟨0, Nat.zero_lt_succ m, ?_⟩
      have hsub : ((n - 1 : ℕ) : ZMod n) = -1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, zero_sub, Nat.cast_one]
      simpa [← hnext_cast, hhit] using hsub
    · have hfalse : (next == n - 1) = false := by
        simp [beq_eq_false_iff_ne, hhit]
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at h
      rcases ih next h with ⟨j, hj, hpow⟩
      refine ⟨j + 1, Nat.succ_lt_succ hj, ?_⟩
      rw [hnext_cast, ← pow_mul] at hpow
      have hexp : 2 * 2 ^ (j + 1) = 2 ^ (j + 2) := by ring
      rwa [← hexp]

lemma isStrongPRP_spec {n a : ℕ} (hn : 2 < n) (hodd : n % 2 = 1)
    (h : isStrongPRP n a = true) :
    let (s, d) := splitTwos (n - 1)
    ((a : ZMod n) ^ d = 1 ∨ ∃ j < s, (a : ZMod n) ^ (2 ^ j * d) = -1) ∧
      IsUnit (a : ZMod n) := by
  have hn1_pos : 0 < n - 1 := by omega
  have hn1_even : (n - 1) % 2 = 0 := by omega
  rcases splitTwos_spec (n - 1) hn1_pos with ⟨hsd, _⟩
  have hs1 : 1 ≤ (splitTwos (n - 1)).1 := splitTwos_fst_pos hn1_pos hn1_even
  set s := (splitTwos (n - 1)).1
  set d := (splitTwos (n - 1)).2
  set x := powMod a d n
  have hx_eq : x = a ^ d % n := powMod_eq a d n (by omega)
  have hx_cast : (x : ZMod n) = (a : ZMod n) ^ d := by
    rw [hx_eq, ZMod.natCast_mod, Nat.cast_pow]
  have hsub : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, zero_sub, Nat.cast_one]
  unfold isStrongPRP at h
  change (if (x == 1 || x == n - 1) = true then true else checkSquares x n (s - 1)) = true at h
  have hmain : (a : ZMod n) ^ d = 1 ∨ ∃ j < s, (a : ZMod n) ^ (2 ^ j * d) = -1 := by
    by_cases h1 : x = 1 ∨ x = n - 1
    · rcases h1 with hx1 | hxm1
      · left
        rw [← hx_cast, hx1, Nat.cast_one]
      · right
        refine ⟨0, by omega, ?_⟩
        simpa [← hx_cast, hxm1] using hsub
    · push Not at h1
      have hcond : ((x == 1) || (x == n - 1)) = false := by
        simp [beq_eq_false_iff_ne, h1.1, h1.2]
      simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
      rcases checkSquares_sound (by omega) (s - 1) x h with ⟨j, hj, hpow⟩
      right
      refine ⟨j + 1, by omega, ?_⟩
      rw [hx_cast, ← pow_mul, mul_comm d] at hpow
      exact hpow
  have hpow_one : (a : ZMod n) ^ (n - 1) = 1 := by
    rw [← hsd]
    rcases hmain with hd1 | ⟨j, hj, hjm1⟩
    · rw [mul_comm, pow_mul, hd1, one_pow]
    · have hexp : 2 ^ s * d = (2 ^ j * d) * 2 ^ (s - j) := by
        calc 2 ^ s * d = 2 ^ (j + (s - j)) * d := by congr 2; omega
          _ = 2 ^ j * 2 ^ (s - j) * d := by rw [pow_add]
          _ = (2 ^ j * d) * 2 ^ (s - j) := by ring
      rw [hexp, pow_mul, hjm1]
      have hge1 : 1 ≤ s - j := by omega
      have h2even : Even (2 ^ (s - j)) := by
        rw [show s - j = (s - j - 1) + 1 by omega, pow_succ']
        exact even_two_mul _
      exact h2even.neg_one_pow
  have hunit : IsUnit (a : ZMod n) := by
    have hsplit : (a : ZMod n) * (a : ZMod n) ^ (n - 2) = 1 := by
      rw [← pow_succ', show n - 2 + 1 = n - 1 by omega]
      exact hpow_one
    exact isUnit_iff_exists_inv.mpr ⟨_, hsplit⟩
  exact ⟨hmain, hunit⟩

lemma checkBases_sound {n : ℕ} :
    ∀ lo hi : ℕ, checkBases n lo hi = true →
      ∀ a, lo ≤ a → a ≤ hi → isStrongPRP n a = true := by
  intro lo hi
  induction hlen : hi + 1 - lo generalizing lo with
  | zero =>
    intro _ a ha1 ha2
    omega
  | succ k ih =>
    intro h a ha1 ha2
    unfold checkBases at h
    have hnotlt : ¬ hi < lo := by omega
    rw [if_neg hnotlt] at h
    by_cases hlo : isStrongPRP n lo = true
    · rw [if_pos hlo] at h
      by_cases ha : a = lo
      · subst ha; exact hlo
      · exact ih (lo + 1) (by omega) h a (by omega) ha2
    · rw [if_neg hlo] at h
      simp at h

/-- Si todo `u ∈ (ZMod n)ˣ` cumple `u^(n-1) = 1` (Carmichael), entonces `n` es libre de cuadrados. -/
lemma squarefree_of_forall_pow_sub_one_eq_one {n : ℕ} (hn : 2 < n)
    (hcarm : ∀ u : (ZMod n)ˣ, u ^ (n - 1) = 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  rcases hpp with ⟨k, hnk⟩
  set m := p * k
  have hnm : n = p * m := by dsimp [m]; linarith
  have hm_pos : 0 < m := by
    by_contra hm0
    have : m = 0 := by omega
    rw [this, mul_zero] at hnm
    omega
  have hm_lt : m < n := by
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith
  have hm_sq : (m : ZMod n) * (m : ZMod n) = 0 := by
    have hdvd : n ∣ m * m := ⟨k, by dsimp [m]; rw [hnk]; ring⟩
    rw [← Nat.cast_mul]
    exact (ZMod.natCast_eq_zero_iff (m * m) n).mpr hdvd
  have hpow_add : ∀ t : ℕ, (1 + (m : ZMod n)) ^ t = 1 + (t : ZMod n) * (m : ZMod n) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ, ih]
      push_cast
      calc (1 + (t : ZMod n) * (m : ZMod n)) * (1 + (m : ZMod n))
          = 1 + ((t : ZMod n) + 1) * (m : ZMod n) + (t : ZMod n) * ((m : ZMod n) * (m : ZMod n)) := by ring
        _ = 1 + ((t : ZMod n) + 1) * (m : ZMod n) := by rw [hm_sq, mul_zero, add_zero]
  have hunit : IsUnit (1 + (m : ZMod n)) := by
    refine isUnit_iff_exists_inv.mpr ⟨1 - (m : ZMod n), ?_⟩
    calc (1 + (m : ZMod n)) * (1 - (m : ZMod n))
        = 1 - (m : ZMod n) * (m : ZMod n) := by ring
      _ = 1 := by rw [hm_sq, sub_zero]
  rcases hunit with ⟨u, hu⟩
  have hu_pow : (u : ZMod n) ^ (n - 1) = 1 := by
    have := congrArg Units.val (hcarm u)
    simpa using this
  rw [hu, hpow_add (n - 1)] at hu_pow
  have hsub : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, zero_sub, Nat.cast_one]
  rw [hsub, neg_one_mul] at hu_pow
  have hm_zero : (m : ZMod n) = 0 := by
    have : 1 + -(m : ZMod n) - 1 = 1 - 1 := congrArg (· - 1) hu_pow
    simpa using this
  have hdvd_m : n ∣ m := (ZMod.natCast_eq_zero_iff m n).mp hm_zero
  have hle : n ≤ m := Nat.le_of_dvd hm_pos hdvd_m
  omega

/-- Para todo `n ≥ 5` impar y compuesto, existe un subgrupo propio `H < (ZMod n)ˣ`
    que contiene a todas las bases fuertes (mentirosos de Miller-Rabin). -/
lemma exists_proper_subgroup_containing_strongPRP {n : ℕ} (hn5 : 5 ≤ n)
    (hodd : n % 2 = 1) (hcomp : ¬ Nat.Prime n) :
    let (s, d) := splitTwos (n - 1)
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod n)ˣ,
        ((u : ZMod n) ^ d = 1 ∨ ∃ j < s, (u : ZMod n) ^ (2 ^ j * d) = -1) → u ∈ H := by
  have hn1_pos : 0 < n - 1 := by omega
  have hn1_even : (n - 1) % 2 = 0 := by omega
  rcases splitTwos_spec (n - 1) hn1_pos with ⟨hsd, hd_odd⟩
  have hs1 : 1 ≤ (splitTwos (n - 1)).1 := splitTwos_fst_pos hn1_pos hn1_even
  set s := (splitTwos (n - 1)).1
  set d := (splitTwos (n - 1)).2
  dsimp only
  by_cases hcarm : ∀ u : (ZMod n)ˣ, u ^ (n - 1) = 1
  · -- Caso Carmichael: n es libre de cuadrados con al menos dos factores primos impares coprimos
    have hsqf : Squarefree n := squarefree_of_forall_pow_sub_one_eq_one (by omega) hcarm
    set p := n.minFac
    set q := n / p
    have hp : Nat.Prime p := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hpq : p * q = n := Nat.mul_div_cancel' hpn
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      have : p ≠ 2 := by
        intro hp2
        rw [hp2] at hpn
        omega
      omega
    have hq3 : 3 ≤ q := by
      have hq1 : q ≠ 1 := by
        intro hq1
        rw [hq1, mul_one] at hpq
        exact hcomp (hpq ▸ hp)
      have hq0 : q ≠ 0 := by
        intro hq0
        rw [hq0, mul_zero] at hpq
        omega
      have hq2 : q ≠ 2 := by
        intro hq2
        rw [hq2] at hpq
        have : (p * 2) % 2 = 0 := by omega
        omega
      match q with
      | 0 => exact absurd rfl hq0
      | 1 => exact absurd rfl hq1
      | 2 => exact absurd rfl hq2
      | _ + 3 => omega
    have hcop : Nat.Coprime p q := by
      rw [hp.coprime_iff_not_dvd]
      intro hpq_dvd
      have hpp : p * p ∣ n := by
        rcases hpq_dvd with ⟨t, ht⟩
        exact ⟨t, by rw [← hpq, ht]; ring⟩
      exact hp.ne_one (Nat.isUnit_iff.mp (hsqf p hpp))
    -- Máximo r < s tal que ∃ u, u^(2^r * d) = -1
    classical
    let S : Finset ℕ := (Finset.range s).filter (fun j => ∃ u : (ZMod n)ˣ, (u : ZMod n) ^ (2 ^ j * d) = -1)
    have h0_mem : 0 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, -1, ?_⟩
      simp only [pow_zero, one_mul, Units.val_neg, Units.val_one]
      have hd_odd' : Odd d := Nat.odd_iff.mpr hd_odd
      exact hd_odd'.neg_one_pow
    have hS_ne : S.Nonempty := ⟨0, h0_mem⟩
    set r := S.max' hS_ne
    have hr_mem : r ∈ S := Finset.max'_mem S hS_ne
    simp only [S, Finset.mem_filter, Finset.mem_range] at hr_mem
    rcases hr_mem with ⟨hr_lt, v, hv⟩
    -- Subgrupo H = {u | u^(2^r * d) ∈ {1, -1}}
    let H : Subgroup (ZMod n)ˣ :=
      { carrier := {u | u ^ (2 ^ r * d) = 1 ∨ u ^ (2 ^ r * d) = -1}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [mul_pow]
          rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [inv_pow]
          rcases ha with ha | ha <;> simp [ha] }
    refine ⟨H, ?_, ?_⟩
    · -- H ≠ ⊤ vía Teorema Chino del Resto en ZMod (p * q) ≃+* ZMod p × ZMod q
      intro htop
      let e : ZMod n ≃+* ZMod p × ZMod q :=
        (ZMod.ringEquivCongr hpq.symm).trans (ZMod.chineseRemainder hcop)
      let ev := Units.map e.toMonoidHom v
      have hvp_unit : IsUnit (e (v : ZMod n)).1 := by
        have h1 : IsUnit (e (v : ZMod n)) := (v.isUnit).map e.toMonoidHom
        exact h1.map (RingHom.fst (ZMod p) (ZMod q))
      rcases hvp_unit with ⟨vp, hvp⟩
      let w_pair : (ZMod p × ZMod q)ˣ :=
        { val := (vp, 1)
          inv := (↑vp⁻¹, 1)
          val_inv := by ext <;> simp
          inv_val := by ext <;> simp }
      let w : (ZMod n)ˣ := Units.map e.symm.toMonoidHom w_pair
      have hw_mem : w ∈ H := by rw [htop]; trivial
      have hew : e (w : ZMod n) = ((vp : ZMod p), (1 : ZMod q)) := by
        change e (e.symm ((vp : ZMod p), (1 : ZMod q))) = ((vp : ZMod p), (1 : ZMod q))
        exact e.apply_symm_apply _
      have hew_pow : e ((w : ZMod n) ^ (2 ^ r * d)) = (-1, 1) := by
        rw [map_pow, hew]
        ext
        · change ((vp : ZMod p) ^ (2 ^ r * d)) = (-1 : ZMod p)
          rw [hvp]
          have h1 := congrArg (fun z => (e z).1) hv
          simpa [map_pow] using h1
        · change ((1 : ZMod q) ^ (2 ^ r * d)) = (1 : ZMod q)
          simp
      have hne1 : (-1 : ZMod p) ≠ 1 := by
        intro h
        have h2 : (2 : ZMod p) = 0 := by
          rw [← one_add_one_eq_two]
          nth_rw 2 [← h]
          ring
        have hdvd2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
        have := Nat.le_of_dvd (by omega) hdvd2
        omega
      have hne2 : (1 : ZMod q) ≠ -1 := by
        intro h
        have h2 : (2 : ZMod q) = 0 := by
          rw [← one_add_one_eq_two]
          nth_rw 2 [h]
          ring
        have hdvd2 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h2)
        have := Nat.le_of_dvd (by omega) hdvd2
        omega
      rcases hw_mem with hw1 | hwm1
      · have h1 := congrArg (fun z => (e z.val).1) hw1
        simp only [Units.val_pow_eq_pow_val, hew_pow, Units.val_one, map_one, Prod.fst_one] at h1
        exact hne1 h1
      · have h2 := congrArg (fun z => (e z.val).2) hwm1
        simp only [Units.val_pow_eq_pow_val, hew_pow, Units.val_neg, Units.val_one, map_neg,
          map_one, Prod.snd_neg, Prod.snd_one] at h2
        exact hne2 h2
    · -- Todo mentiroso fuerte pertenece a H
      intro u hu
      show u ^ (2 ^ r * d) = 1 ∨ u ^ (2 ^ r * d) = -1
      rcases hu with hud | ⟨j, hj, huj⟩
      · left
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_one]
        rw [mul_comm, pow_mul, hud, one_pow]
      · have hjle : j ≤ r := by
          apply Finset.le_max' S j
          simp only [S, Finset.mem_filter, Finset.mem_range]
          exact ⟨hj, u, huj⟩
        by_cases hjeq : j = r
        · right
          subst hjeq
          apply Units.ext
          simpa using huj
        · left
          apply Units.ext
          simp only [Units.val_pow_eq_pow_val, Units.val_one]
          have hexp : 2 ^ r * d = (2 ^ j * d) * 2 ^ (r - j) := by
            calc 2 ^ r * d = 2 ^ (j + (r - j)) * d := by congr 2; omega
              _ = 2 ^ j * 2 ^ (r - j) * d := by rw [pow_add]
              _ = (2 ^ j * d) * 2 ^ (r - j) := by ring
          rw [hexp, pow_mul, huj]
          have h2even : Even (2 ^ (r - j)) := by
            rw [show r - j = (r - j - 1) + 1 by omega, pow_succ']
            exact even_two_mul _
          exact h2even.neg_one_pow
  · -- Caso no-Carmichael: H = ker(u ↦ u^(n-1)) es propio
    push Not at hcarm
    rcases hcarm with ⟨u₀, hu₀⟩
    let H : Subgroup (ZMod n)ˣ :=
      { carrier := {u | u ^ (n - 1) = 1}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [mul_pow, ha, hb, one_mul]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [inv_pow, ha, inv_one] }
    refine ⟨H, ?_, ?_⟩
    · intro htop
      have : u₀ ∈ H := by rw [htop]; trivial
      exact hu₀ this
    · intro u hu
      show u ^ (n - 1) = 1
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      rw [← hsd]
      rcases hu with hud | ⟨j, hj, huj⟩
      · rw [mul_comm, pow_mul, hud, one_pow]
      · have hexp : 2 ^ s * d = (2 ^ j * d) * 2 ^ (s - j) := by
          calc 2 ^ s * d = 2 ^ (j + (s - j)) * d := by congr 2; omega
            _ = 2 ^ j * 2 ^ (s - j) * d := by rw [pow_add]
            _ = (2 ^ j * d) * 2 ^ (s - j) := by ring
        rw [hexp, pow_mul, huj]
        have h2even : Even (2 ^ (s - j)) := by
          rw [show s - j = (s - j - 1) + 1 by omega, pow_succ']
          exact even_two_mul _
        exact h2even.neg_one_pow

/-- De un subgrupo propio `H < (ZMod n)ˣ` se obtiene un carácter de Dirichlet
    no principal `χ (mod n)` que vale `1` en todo `u ∈ H`. -/
lemma exists_nontriv_dirichletChar_of_proper_subgroup {n : ℕ} [NeZero n]
    {H : Subgroup (ZMod n)ˣ} (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ n, χ ≠ 1 ∧ ∀ u ∈ H, χ (u : ZMod n) = 1 := by
  have hexp_ne : Monoid.exponent (ZMod n)ˣ ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have : NeZero (Monoid.exponent (ZMod n)ˣ) := ⟨hexp_ne⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod n)ˣ) :=
    ⟨⟨Complex.exp (2 * Real.pi * Complex.I / (Monoid.exponent (ZMod n)ˣ : ℂ)),
      Complex.isPrimitiveRoot_exp _ hexp_ne⟩, inferInstance⟩
  let e := MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ
  have hdual_ne_bot : (e H).ofDual ≠ ⊥ := by
    intro hbot
    have htop : e H = ⊤ := by
      apply OrderDual.ofDual.injective
      simpa using hbot
    exact hH (e.injective (htop.trans (map_top e).symm))
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hdual_ne_bot
  rcases hdual_ne_bot with ⟨⟨χ, hχmem⟩, hχne⟩
  refine ⟨χ, ?_, ?_⟩
  · intro h1
    exact hχne (Subtype.ext h1)
  · exact (MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff (M := ZMod n) (R := ℂ)).mp hχmem

/-- Hipótesis de Riemann Generalizada (GRH) para funciones L de Dirichlet:
    todo cero de `L(s, χ)` en la banda crítica `0 < Re(s) < 1` satisface `Re(s) = 1/2`. -/
def DirichletGRH : Prop :=
  ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- Caso elemental de Bach: cuando `bachBound n = n - 1` (en particular todo `5 ≤ n ≤ 129`),
    todo carácter no principal `χ (mod n)` toma un valor `≠ 1` en algún `2 ≤ a ≤ n - 1` sin usar GRH. -/
theorem bach_least_nonresidue_small {n : ℕ} (hn : 5 ≤ n) (hbound : bachBound n = n - 1)
    (χ : DirichletCharacter ℂ n) (hχ : χ ≠ 1) :
    ∃ a : ℕ, 2 ≤ a ∧ a ≤ bachBound n ∧ χ a ≠ 1 := by
  have : NeZero n := ⟨by omega⟩
  have hex : ∃ x : ZMod n, IsUnit x ∧ χ x ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hχ
    ext x
    rw [hall x.1 x.isUnit, MulChar.one_apply x.isUnit]
  rcases hex with ⟨x, hx_unit, hχx⟩
  refine ⟨x.val, ?_, ?_, ?_⟩
  · have hne0 : x.val ≠ 0 := by
      intro h0
      have hx0 : x = 0 := by
        rw [← ZMod.natCast_zmod_val x, h0, Nat.cast_zero]
      rw [hx0] at hx_unit
      have h01 : (0 : ZMod n) = 1 := isUnit_zero_iff.mp hx_unit
      have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
      exact zero_ne_one h01
    have hne1 : x.val ≠ 1 := by
      intro h1
      have hx1 : x = 1 := by
        rw [← ZMod.natCast_zmod_val x, h1, Nat.cast_one]
      rw [hx1, map_one] at hχx
      exact hχx rfl
    omega
  · rw [hbound]
    have hlt : x.val < n := ZMod.val_lt x
    omega
  · rwa [ZMod.natCast_zmod_val]

/-- Teorema analítico de Bach (1990) bajo GRH para `n` grande (`2 * (log₂ n + 1)² < n - 1`, i.e., `n ≥ 130`):
    para todo carácter de Dirichlet no principal `χ (mod n)`,
    existe un natural `a` con `2 ≤ a ≤ bachBound n` tal que `χ a ≠ 1`. -/
theorem bach_least_nonresidue_large (hGRH : DirichletGRH) {n : ℕ} (hn : 5 ≤ n)
    (hlarge : 2 * (Nat.log2 n + 1) ^ 2 < n - 1)
    (χ : DirichletCharacter ℂ n) (hχ : χ ≠ 1) :
    ∃ a : ℕ, 2 ≤ a ∧ a ≤ bachBound n ∧ χ a ≠ 1 := by
  sorry

/-- Teorema analítico de Bach (1990) bajo GRH:
    para todo `n ≥ 5` y todo carácter de Dirichlet no principal `χ (mod n)`,
    existe un natural `a` con `2 ≤ a ≤ bachBound n` tal que `χ a ≠ 1`. -/
theorem bach_least_nonresidue (hGRH : DirichletGRH) {n : ℕ} (hn : 5 ≤ n)
    (χ : DirichletCharacter ℂ n) (hχ : χ ≠ 1) :
    ∃ a : ℕ, 2 ≤ a ∧ a ≤ bachBound n ∧ χ a ≠ 1 := by
  by_cases h : n - 1 ≤ 2 * (Nat.log2 n + 1) ^ 2
  · exact bach_least_nonresidue_small hn (min_eq_left h) χ hχ
  · exact bach_least_nonresidue_large hGRH hn (by omega) χ hχ

/-- Dirección de corrección (soundness) de Miller-Rabin determinista bajo GRH:
    demostrada completamente a partir de `bach_least_nonresidue` (sin `sorry` propio). -/
theorem isPrimeMR_sound (hGRH : DirichletGRH) {n : ℕ} (h : isPrimeMR n = true) :
    Nat.Prime n := by
  unfold isPrimeMR at h
  by_cases hn2 : n < 2
  · rw [if_pos hn2] at h; simp at h
  · rw [if_neg hn2] at h
    by_cases h23 : n = 2 ∨ n = 3
    · rcases h23 with rfl | rfl <;> decide
    · push Not at h23
      have hcond : ((n == 2) || (n == 3)) = false := by
        simp [beq_eq_false_iff_ne, h23.1, h23.2]
      simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
      by_cases heven : n % 2 = 0
      · simp only [heven, beq_self_eq_true, ↓reduceIte] at h
        simp at h
      · have hodd_bool : (n % 2 == 0) = false := by
          simp [beq_eq_false_iff_ne, heven]
        simp only [hodd_bool, Bool.false_eq_true, ↓reduceIte] at h
        have hn5 : 5 ≤ n := by omega
        have hodd : n % 2 = 1 := by omega
        have hall : ∀ a, 2 ≤ a → a ≤ bachBound n → isStrongPRP n a = true :=
          checkBases_sound 2 (bachBound n) h
        by_contra hcomp
        haveI : NeZero n := ⟨by omega⟩
        rcases exists_proper_subgroup_containing_strongPRP hn5 hodd hcomp with ⟨H, hH_ne, hH_mem⟩
        rcases exists_nontriv_dirichletChar_of_proper_subgroup hH_ne with ⟨χ, hχ_ne, hχ_triv⟩
        rcases bach_least_nonresidue hGRH hn5 χ hχ_ne with ⟨a, ha2, habach, hχa⟩
        have hprp : isStrongPRP n a = true := hall a ha2 habach
        rcases isStrongPRP_spec (by omega) hodd hprp with ⟨hspec, hunit⟩
        rcases hunit with ⟨u, hu⟩
        have huH : u ∈ H := hH_mem u (by simpa [hu] using hspec)
        have hχu : χ (u : ZMod n) = 1 := hχ_triv u huH
        rw [hu] at hχu
        exact hχa hχu

/-- Teorema de Bach (1990) bajo GRH: `isPrimeMR n = true ↔ Nat.Prime n`. -/
theorem isPrimeMR_iff_prime (hGRH : DirichletGRH) (n : ℕ) :
    isPrimeMR n = true ↔ Nat.Prime n :=
  ⟨isPrimeMR_sound hGRH, isPrimeMR_of_prime⟩

/-- Escáner rápido ejecutable usando `isPrimeMR`. -/
def scanPrimeFast (k : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
      if isPrimeMR k then some k
      else scanPrimeFast (k + 1) fuel

lemma scanPrimeFast_sound (hGRH : DirichletGRH) {k fuel p : ℕ}
    (h : scanPrimeFast k fuel = some p) :
    Nat.Prime p ∧ k ≤ p ∧ p < k + fuel := by
  induction fuel generalizing k with
  | zero => simp [scanPrimeFast] at h
  | succ f ih =>
    unfold scanPrimeFast at h
    split_ifs at h with hmr
    · injection h with hEq
      subst hEq
      exact ⟨(isPrimeMR_iff_prime hGRH k).mp hmr, le_rfl, by omega⟩
    · rcases ih h with ⟨hp', hle, hlt⟩
      exact ⟨hp', by omega, by omega⟩

lemma scanPrimeFast_isSome_of_exists (hGRH : DirichletGRH) {k fuel : ℕ}
    (hex : ∃ p, Nat.Prime p ∧ k ≤ p ∧ p < k + fuel) :
    (scanPrimeFast k fuel).isSome := by
  induction fuel generalizing k with
  | zero =>
    rcases hex with ⟨p, _, hle, hlt⟩
    omega
  | succ f ih =>
    unfold scanPrimeFast
    split_ifs with hmr
    · rfl
    · apply ih
      rcases hex with ⟨p, hp', hle, hlt⟩
      have hne : k ≠ p := by
        intro hEq
        subst hEq
        exact hmr ((isPrimeMR_iff_prime hGRH k).mpr hp')
      exact ⟨p, hp', by omega, by omega⟩

lemma scanPrimeFast_always_succeeds
    (hRH : RiemannHypothesis) (hGRH : DirichletGRH) {x : ℕ} (hx : 4 ≤ x) :
    (scanPrimeFast (x + 1) (VerifiedNextPrime.searchBound x)).isSome := by
  apply scanPrimeFast_isSome_of_exists hGRH
  have hxR : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  rcases ShortIntervalPrimes.exists_prime_in_short_interval hRH hxR with ⟨p, hp, hgt, hle⟩
  have hB := VerifiedNextPrime.real_bound_lt_searchBound hx
  refine ⟨p, hp, ?_, ?_⟩
  · have : x < p := by exact_mod_cast hgt
    omega
  · have hltR : (p : ℝ) < ((x + VerifiedNextPrime.searchBound x : ℕ) : ℝ) := by
      push_cast; linarith
    have hltN : p < x + VerifiedNextPrime.searchBound x := by exact_mod_cast hltR
    omega

def nextPrimeFast (hRH : RiemannHypothesis) (hGRH : DirichletGRH)
    (x : ℕ) (hx : 4 ≤ x) : ℕ :=
  (scanPrimeFast (x + 1) (VerifiedNextPrime.searchBound x)).get
    (scanPrimeFast_always_succeeds hRH hGRH hx)

theorem nextPrimeFast_isPrime (hRH : RiemannHypothesis) (hGRH : DirichletGRH)
    (x : ℕ) (hx : 4 ≤ x) :
    Nat.Prime (nextPrimeFast hRH hGRH x hx) := by
  have h := Option.some_get (scanPrimeFast_always_succeeds hRH hGRH hx)
  exact (scanPrimeFast_sound hGRH h.symm).1

theorem nextPrimeFast_gt (hRH : RiemannHypothesis) (hGRH : DirichletGRH)
    (x : ℕ) (hx : 4 ≤ x) :
    x < nextPrimeFast hRH hGRH x hx := by
  unfold nextPrimeFast
  have h := Option.some_get (scanPrimeFast_always_succeeds hRH hGRH hx)
  have hge := (scanPrimeFast_sound hGRH h.symm).2.1
  omega

theorem nextPrimeFast_le_bound (hRH : RiemannHypothesis) (hGRH : DirichletGRH)
    (x : ℕ) (hx : 4 ≤ x) :
    nextPrimeFast hRH hGRH x hx ≤ x + VerifiedNextPrime.searchBound x := by
  unfold nextPrimeFast
  have h := Option.some_get (scanPrimeFast_always_succeeds hRH hGRH hx)
  have hlt := (scanPrimeFast_sound hGRH h.symm).2.2
  omega

end DeterministicMR

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Data.Nat.Prime.Basic

open Complex Real ArithmeticFunction

namespace ShortIntervalPrimes

/-! ### Definiciones base -/

/-- Semiancho logarítmico h = (1/2) * ln(1 + Δ/x). -/
noncomputable def halfWidth (x Δ : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + Δ / x)

/-- Centro logarítmico c = (1/2) * (ln x + ln(x + Δ)). -/
noncomputable def logCenter (x Δ : ℝ) : ℝ :=
  (1 / 2) * (Real.log x + Real.log (x + Δ))

/-- Kernel triangular (autoconvolución m = 2) con soporte en [-h, h]. -/
noncomputable def triKernel (h t : ℝ) : ℝ :=
  (1 / h) * max 0 (1 - |t| / h)

/-- Peso suave w(u) = e^{-u/2} * g_0(u - c) con soporte en [ln x, ln(x + Δ)]. -/
noncomputable def smoothWeight (x Δ u : ℝ) : ℝ :=
  Real.exp (-u / 2) * triKernel (halfWidth x Δ) (u - logCenter x Δ)

/-- Suma finita S(x, Δ) = ∑_{x < n ≤ x + Δ} Λ(n) * w(ln n). -/
noncomputable def weightedVonMangoldt (x Δ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor (x + Δ)),
    (vonMangoldt n) * smoothWeight x Δ (Real.log n)

/-- Suma de Λ(n) sobre potencias propias de primos (no primos) hasta N. -/
noncomputable def properPrimePowerSum (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n), (vonMangoldt n : ℝ)

/-- Transformada de Mellin cerrada de `smoothWeight x Δ` en s ∈ ℂ. -/
noncomputable def mellinTriWeight (x Δ : ℝ) (s : ℂ) : ℂ :=
  let z : ℂ := s - (1 / 2 : ℂ)
  let h : ℂ := (halfWidth x Δ : ℂ)
  let c : ℂ := (logCenter x Δ : ℂ)
  Complex.exp (z * c) * (Complex.sinh (z * h / 2) / (z * h / 2)) ^ 2

/-- Predicado de cero no trivial de ζ(s). -/
def IsNontrivialZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1

/-! ### Propiedades elementales del kernel triangular -/

lemma triKernel_nonneg {h : ℝ} (hh : 0 < h) (t : ℝ) : 0 ≤ triKernel h t := by
  unfold triKernel
  exact mul_nonneg (by positivity) (le_max_left _ _)

lemma triKernel_le_inv {h : ℝ} (hh : 0 < h) (t : ℝ) : triKernel h t ≤ 1 / h := by
  unfold triKernel
  have h1 : 1 - |t| / h ≤ 1 := by
    have : 0 ≤ |t| / h := div_nonneg (abs_nonneg t) hh.le
    linarith
  have hmax : max 0 (1 - |t| / h) ≤ 1 := max_le (by norm_num) h1
  calc
    (1 / h) * max 0 (1 - |t| / h) ≤ (1 / h) * 1 :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = 1 / h := mul_one _

lemma smoothWeight_le_inv_mul_sqrt
    {x Δ : ℝ} {n : ℕ} (hx : 0 < x) (hΔ : 0 < Δ) (hxn : x < (n : ℝ)) :
    smoothWeight x Δ (Real.log n) ≤ 1 / (halfWidth x Δ * Real.sqrt x) := by
  unfold smoothWeight
  have hn0 : 0 < (n : ℝ) := lt_trans hx hxn
  have hh : 0 < halfWidth x Δ := by
    unfold halfWidth
    exact mul_pos (by norm_num) (Real.log_pos (lt_add_of_pos_right 1 (div_pos hΔ hx)))
  have hexp : Real.exp (-Real.log n / 2) = (Real.sqrt n)⁻¹ := by
    rw [neg_div, Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
    ring_nf
  have hsqrt : (Real.sqrt n)⁻¹ ≤ (Real.sqrt x)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt hxn.le)
  have htri : triKernel (halfWidth x Δ) (Real.log n - logCenter x Δ) ≤ 1 / halfWidth x Δ :=
    triKernel_le_inv hh _
  rw [hexp]
  calc (Real.sqrt n)⁻¹ * triKernel (halfWidth x Δ) (Real.log n - logCenter x Δ)
      ≤ (Real.sqrt x)⁻¹ * (1 / halfWidth x Δ) :=
        mul_le_mul hsqrt htri (triKernel_nonneg hh _) (by positivity)
    _ = 1 / (halfWidth x Δ * Real.sqrt x) := by
        rw [one_div, one_div, mul_inv, mul_comm]

/-! ### Transformada de Mellin en s = 1 y en la línea crítica (Re(ρ) = 1/2) -/

lemma mellinTriWeight_at_one_ge_sqrt {x Δ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) :
    Real.sqrt x ≤ (mellinTriWeight x Δ 1).re := by
  have hh : 0 < halfWidth x Δ := by
    unfold halfWidth
    exact mul_pos (by norm_num) (Real.log_pos (lt_add_of_pos_right 1 (div_pos hΔ hx)))
  have hreal :
      (mellinTriWeight x Δ 1).re =
        Real.exp (logCenter x Δ / 2) * (Real.sinh (halfWidth x Δ / 4) / (halfWidth x Δ / 4)) ^ 2 := by
    dsimp only [mellinTriWeight]
    have hz : (1 : ℂ) - (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hz]
    have harg1 : ((1 / 2 : ℝ) : ℂ) * (logCenter x Δ : ℂ) = ((logCenter x Δ / 2 : ℝ) : ℂ) := by
      push_cast; ring
    have harg2 : ((1 / 2 : ℝ) : ℂ) * (halfWidth x Δ : ℂ) / 2 = ((halfWidth x Δ / 4 : ℝ) : ℂ) := by
      push_cast; ring
    rw [harg1, harg2, ← Complex.ofReal_exp, ← Complex.ofReal_sinh,
        ← Complex.ofReal_div, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hreal]
  have hsinh : 1 ≤ Real.sinh (halfWidth x Δ / 4) / (halfWidth x Δ / 4) := by
    have ht : 0 < halfWidth x Δ / 4 := by linarith
    rw [one_le_div ht]
    have hmono : Monotone (fun t : ℝ => Real.sinh t - t) := by
      apply monotone_of_deriv_nonneg (Real.differentiable_sinh.sub differentiable_id)
      intro t
      rw [deriv_sub Real.differentiable_sinh.differentiableAt differentiableAt_id,
          Real.deriv_sinh, deriv_id']
      linarith [Real.one_le_cosh t]
    have h0 := hmono ht.le
    simp only [Real.sinh_zero, sub_zero] at h0
    linarith
  have hexp : Real.sqrt x ≤ Real.exp (logCenter x Δ / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    apply Real.exp_le_exp.mpr
    unfold logCenter
    have hlog : Real.log x ≤ Real.log (x + Δ) := Real.log_le_log hx (by linarith)
    linarith
  have hsq : 1 ≤ (Real.sinh (halfWidth x Δ / 4) / (halfWidth x Δ / 4)) ^ 2 := by nlinarith
  calc Real.sqrt x
      ≤ Real.exp (logCenter x Δ / 2) * 1 := by linarith
    _ ≤ Real.exp (logCenter x Δ / 2) *
          (Real.sinh (halfWidth x Δ / 4) / (halfWidth x Δ / 4)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le

lemma norm_mellinTriWeight_on_critical_line
    {x Δ : ℝ} {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖mellinTriWeight x Δ ρ‖ =
      (Real.sin (ρ.im * halfWidth x Δ / 2) / (ρ.im * halfWidth x Δ / 2)) ^ 2 := by
  unfold mellinTriWeight
  set h := halfWidth x Δ
  set c := logCenter x Δ
  set γ := ρ.im
  have hz : ρ - (1 / 2 : ℂ) = (γ : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hre]
    · simp [γ]
  rw [hz]
  have hexp_norm : ‖Complex.exp ((γ : ℂ) * Complex.I * (c : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have : ((γ : ℂ) * Complex.I * (c : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  have harg : (γ : ℂ) * Complex.I * (h : ℂ) / 2 = ((γ * h / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [norm_mul, hexp_norm, one_mul, harg, norm_pow, norm_div]
  rw [Complex.sinh_mul_I, norm_mul, Complex.norm_I, mul_one,
      norm_mul, Complex.norm_I, mul_one,
      ← Complex.ofReal_sin, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_div, sq_abs]

/-! ### Las 3 cajas analíticas clásicas -/

/-! ### Cota elemental de potencias propias de primos (Erdős / Primorial) -/

/-- Cota de Chebyshev vía `primorial_le_four_pow`: `∑_{p ≤ m} ln p ≤ m · ln 4`. -/
lemma chebyshevTheta_le_mul_log_four (m : ℕ) :
    ∑ p ∈ (Finset.range (m + 1)).filter Nat.Prime, Real.log (p : ℝ) ≤
      (m : ℝ) * Real.log 4 := by
  have hprod_ne : ∀ p ∈ (Finset.range (m + 1)).filter Nat.Prime, (p : ℝ) ≠ 0 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.cast_ne_zero.mpr hp.2.ne_zero
  have hsum :
      ∑ p ∈ (Finset.range (m + 1)).filter Nat.Prime, Real.log (p : ℝ) =
        Real.log ((primorial m : ℕ) : ℝ) := by
    rw [← Real.log_prod hprod_ne]
    congr 1
    unfold primorial
    push_cast
    rfl
  rw [hsum]
  have hpos : (0 : ℝ) < (primorial m : ℝ) := by
    exact_mod_cast primorial_pos m
  have hle : ((primorial m : ℕ) : ℝ) ≤ (4 : ℝ) ^ m := by
    exact_mod_cast primorial_le_four_pow m
  calc Real.log ((primorial m : ℕ) : ℝ)
      ≤ Real.log ((4 : ℝ) ^ m) := Real.log_le_log hpos hle
    _ = (m : ℝ) * Real.log 4 := Real.log_pow 4 m

/-- Caracterización explícita de potencias de primos usando `minFac` y `Nat.log`. -/
lemma isPrimePow_eq_minFac_pow {n : ℕ} (hn : IsPrimePow n) :
    Nat.Prime n.minFac ∧ 1 ≤ Nat.log n.minFac n ∧ n.minFac ^ Nat.log n.minFac n = n := by
  rw [isPrimePow_nat_iff] at hn
  rcases hn with ⟨p, k, hp, hk, rfl⟩
  have hmin : (p ^ k).minFac = p := by
    have hdvd : (p ^ k).minFac ∣ p ^ k := Nat.minFac_dvd (p ^ k)
    have hprime : Nat.Prime (p ^ k).minFac := Nat.minFac_prime (by
      have := Nat.one_lt_pow hk.ne' hp.one_lt
      omega)
    have hdp : (p ^ k).minFac ∣ p := hprime.dvd_of_dvd_pow hdvd
    exact (hp.eq_one_or_self_of_dvd _ hdp).resolve_left hprime.ne_one
  rw [hmin, Nat.log_pow hp.one_lt]
  exact ⟨hp, hk, rfl⟩

/-- Suma de `ln (n.minFac)` sobre las potencias `p^k ≤ Y` con exponente fijo `k ≥ 1`. -/
lemma sum_exact_pow_le {Y : ℝ} (hY : 1 ≤ Y) {k : ℕ} (hk : 1 ≤ k) :
    ∑ n ∈ (Finset.Icc 1 (Nat.floor Y)).filter (fun n => IsPrimePow n ∧ Nat.log n.minFac n = k),
      Real.log (n.minFac : ℝ) ≤
      Y ^ (1 / (k : ℝ)) * Real.log 4 := by
  have hY0 : 0 < Y := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set m := Nat.floor (Y ^ (1 / (k : ℝ)))
  have hmaps :
      ∀ n ∈ (Finset.Icc 1 (Nat.floor Y)).filter (fun n => IsPrimePow n ∧ Nat.log n.minFac n = k),
        n.minFac ∈ (Finset.range (m + 1)).filter Nat.Prime := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hn ⊢
    rcases hn with ⟨⟨_, hnY⟩, hpp, hlog⟩
    rcases isPrimePow_eq_minFac_pow hpp with ⟨hp, _, heq⟩
    rw [hlog] at heq
    have hp_pow_le : (n.minFac : ℝ) ^ (k : ℝ) ≤ Y := by
      have h1 : (n.minFac ^ k : ℕ) ≤ Nat.floor Y := by rw [heq]; exact hnY
      have h2 : ((n.minFac ^ k : ℕ) : ℝ) ≤ Y :=
        le_trans (by exact_mod_cast h1) (Nat.floor_le hY0.le)
      simpa [Real.rpow_natCast] using h2
    have hp_le : (n.minFac : ℝ) ≤ Y ^ (1 / (k : ℝ)) := by
      have hpow := Real.rpow_le_rpow (by positivity) hp_pow_le (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ))
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hk0.ne', Real.rpow_one] at hpow
      exact hpow
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hp_le), hp⟩
  have hinj :
      Set.InjOn Nat.minFac
        ↑((Finset.Icc 1 (Nat.floor Y)).filter (fun n => IsPrimePow n ∧ Nat.log n.minFac n = k)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    have ha_eq := (isPrimePow_eq_minFac_pow ha.2.1).2.2
    have hb_eq := (isPrimePow_eq_minFac_pow hb.2.1).2.2
    rw [ha.2.2] at ha_eq
    rw [hb.2.2] at hb_eq
    rw [← ha_eq, ← hb_eq, hab]
  have hsum_le :
      ∑ n ∈ (Finset.Icc 1 (Nat.floor Y)).filter (fun n => IsPrimePow n ∧ Nat.log n.minFac n = k),
        Real.log (n.minFac : ℝ) ≤
      ∑ p ∈ (Finset.range (m + 1)).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [← Finset.sum_image (f := fun p : ℕ => Real.log (p : ℝ)) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨n, hn, rfl⟩
      exact hmaps n hn
    · intro p hp _
      rw [Finset.mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
  have hm_le : (m : ℝ) ≤ Y ^ (1 / (k : ℝ)) := Nat.floor_le (by positivity)
  have hlog4_pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc ∑ n ∈ (Finset.Icc 1 (Nat.floor Y)).filter (fun n => IsPrimePow n ∧ Nat.log n.minFac n = k),
          Real.log (n.minFac : ℝ)
      ≤ ∑ p ∈ (Finset.range (m + 1)).filter Nat.Prime, Real.log (p : ℝ) := hsum_le
    _ ≤ (m : ℝ) * Real.log 4 := chebyshevTheta_le_mul_log_four m
    _ ≤ Y ^ (1 / (k : ℝ)) * Real.log 4 := mul_le_mul_of_nonneg_right hm_le hlog4_pos

/-- Suma de `ln (n.minFac)` sobre todas las potencias `p^k ≤ Y` con `k ≥ 6`. -/
lemma sum_high_pow_le {Y : ℝ} (hY : 1 ≤ Y) :
    ∑ n ∈ (Finset.Icc 1 (Nat.floor Y)).filter (fun n => IsPrimePow n ∧ 6 ≤ Nat.log n.minFac n),
      Real.log (n.minFac : ℝ) ≤
      Y ^ (1 / (6 : ℝ)) * Real.log Y := by
  have hY0 : 0 < Y := by linarith
  set N := Nat.floor Y
  set m := Nat.floor (Y ^ (1 / (6 : ℝ)))
  set S := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ 6 ≤ Nat.log n.minFac n)
  have hmaps : ∀ n ∈ S, n.minFac ∈ Finset.Icc 1 m := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨_, hnN⟩, hpp, hk6⟩
    rcases isPrimePow_eq_minFac_pow hpp with ⟨hp, _, heq⟩
    have hp6 : n.minFac ^ 6 ≤ n :=
      le_trans (Nat.pow_le_pow_right hp.pos hk6) heq.le
    have hp_pow_le : (n.minFac : ℝ) ^ (6 : ℝ) ≤ Y := by
      have h1 : (n.minFac ^ 6 : ℕ) ≤ N := le_trans hp6 hnN
      have h2 : ((n.minFac ^ 6 : ℕ) : ℝ) ≤ Y :=
        le_trans (by exact_mod_cast h1) (Nat.floor_le hY0.le)
      simpa [Real.rpow_natCast] using h2
    have hp_le : (n.minFac : ℝ) ≤ Y ^ (1 / (6 : ℝ)) := by
      have hpow := Real.rpow_le_rpow (by positivity) hp_pow_le (by positivity : (0 : ℝ) ≤ 1 / (6 : ℝ))
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel (by norm_num : (6 : ℝ) ≠ 0), Real.rpow_one] at hpow
      exact hpow
    exact ⟨hp.pos, Nat.le_floor hp_le⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ p ∈ Finset.Icc 1 m,
      ∑ n ∈ S.filter (fun n => n.minFac = p), Real.log (n.minFac : ℝ) ≤ Real.log Y := by
    intro p _
    by_cases hp : Nat.Prime p
    · have hcard : (S.filter (fun n => n.minFac = p)).card ≤ Nat.log p N := by
        have hmaps_k :
            ∀ n ∈ S.filter (fun n => n.minFac = p),
              Nat.log p n ∈ Finset.Icc 1 (Nat.log p N) := by
          intro n hn
          simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
          rcases hn with ⟨⟨⟨_, hnN⟩, _, hk6⟩, hmin⟩
          rw [hmin] at hk6
          exact ⟨by omega, Nat.log_mono_right hnN⟩
        have hinj_k : Set.InjOn (Nat.log p) ↑(S.filter (fun n => n.minFac = p)) := by
          intro a ha b hb hab
          simp only [S, Finset.mem_coe, Finset.mem_filter] at ha hb
          have ha_eq := (isPrimePow_eq_minFac_pow ha.1.2.1).2.2
          have hb_eq := (isPrimePow_eq_minFac_pow hb.1.2.1).2.2
          rw [ha.2] at ha_eq
          rw [hb.2] at hb_eq
          rw [← ha_eq, ← hb_eq, hab]
        calc (S.filter (fun n => n.minFac = p)).card
            = ((S.filter (fun n => n.minFac = p)).image (Nat.log p)).card :=
                (Finset.card_image_of_injOn hinj_k).symm
          _ ≤ (Finset.Icc 1 (Nat.log p N)).card := by
                apply Finset.card_le_card
                intro k hk
                rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
                exact hmaps_k n hn
          _ = Nat.log p N := by simp
      have hsum_const :
          ∑ n ∈ S.filter (fun n => n.minFac = p), Real.log (n.minFac : ℝ) =
            ((S.filter (fun n => n.minFac = p)).card : ℝ) * Real.log (p : ℝ) := by
        rw [Finset.sum_congr rfl (fun n hn => by
          rw [(Finset.mem_filter.mp hn).2])]
        simp
      rw [hsum_const]
      have hNpos : 0 < N := Nat.floor_pos.mpr hY
      have hpow_le : ((p ^ Nat.log p N : ℕ) : ℝ) ≤ Y :=
        le_trans (by exact_mod_cast Nat.pow_log_le_self p hNpos.ne') (Nat.floor_le hY0.le)
      have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      calc ((S.filter (fun n => n.minFac = p)).card : ℝ) * Real.log (p : ℝ)
          ≤ (Nat.log p N : ℝ) * Real.log (p : ℝ) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlogp_nonneg
        _ = Real.log ((p : ℝ) ^ Nat.log p N) := (Real.log_pow (p : ℝ) _).symm
        _ ≤ Real.log Y :=
            Real.log_le_log (pow_pos (by exact_mod_cast hp.pos) _) (by exact_mod_cast hpow_le)
    · have hempty : S.filter (fun n => n.minFac = p) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro n hn hmin
        simp only [S, Finset.mem_filter] at hn
        exact hp (hmin ▸ (isPrimePow_eq_minFac_pow hn.2.1).1)
      rw [hempty, Finset.sum_empty]
      exact Real.log_nonneg hY
  calc ∑ p ∈ Finset.Icc 1 m, ∑ n ∈ S.filter (fun n => n.minFac = p), Real.log (n.minFac : ℝ)
      ≤ ∑ _p ∈ Finset.Icc 1 m, Real.log Y := Finset.sum_le_sum hfiber
    _ = (m : ℝ) * Real.log Y := by simp
    _ ≤ Y ^ (1 / (6 : ℝ)) * Real.log Y :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (Real.log_nonneg hY)

lemma properPrimePowerSum_le_two_sqrt {Y : ℝ} (hY : 10^5 ≤ Y) :
    properPrimePowerSum (Nat.floor Y) ≤ 2 * Real.sqrt Y := by
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  set N := Nat.floor Y
  -- Paso 1: reducir a potencias propias con `IsPrimePow n` y `2 ≤ Nat.log n.minFac n`
  have hstep1 :
      properPrimePowerSum N ≤
        Y ^ (1 / (2 : ℝ)) * Real.log 4 + Y ^ (1 / (3 : ℝ)) * Real.log 4 +
        Y ^ (1 / (4 : ℝ)) * Real.log 4 + Y ^ (1 / (5 : ℝ)) * Real.log 4 +
        Y ^ (1 / (6 : ℝ)) * Real.log Y := by
    unfold properPrimePowerSum
    set A := (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n)
    set S2 := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ Nat.log n.minFac n = 2)
    set S3 := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ Nat.log n.minFac n = 3)
    set S4 := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ Nat.log n.minFac n = 4)
    set S5 := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ Nat.log n.minFac n = 5)
    set S6 := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ 6 ≤ Nat.log n.minFac n)
    have hrewrite :
        ∑ n ∈ A, (vonMangoldt n : ℝ) =
          ∑ n ∈ A.filter IsPrimePow, Real.log (n.minFac : ℝ) := by
      rw [← Finset.sum_filter_of_ne (p := IsPrimePow)]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_filter] at hn
        simp [ArithmeticFunction.vonMangoldt_apply, hn.2]
      · intro n _ hne
        exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
    rw [hrewrite]
    have hsub : A.filter IsPrimePow ⊆ (((S2 ∪ S3) ∪ S4) ∪ S5) ∪ S6 := by
      intro n hn
      simp only [A, S2, S3, S4, S5, S6, Finset.mem_filter, Finset.mem_union] at hn ⊢
      rcases hn with ⟨⟨hnIcc, hnp⟩, hpp⟩
      rcases isPrimePow_eq_minFac_pow hpp with ⟨hp, hk1, heq⟩
      have hk2 : 2 ≤ Nat.log n.minFac n := by
        by_contra hlt
        have hk_eq : Nat.log n.minFac n = 1 := by omega
        rw [hk_eq, pow_one] at heq
        exact hnp (heq ▸ hp)
      by_cases h2 : Nat.log n.minFac n = 2
      · left; left; left; left; exact ⟨hnIcc, hpp, h2⟩
      · by_cases h3 : Nat.log n.minFac n = 3
        · left; left; left; right; exact ⟨hnIcc, hpp, h3⟩
        · by_cases h4 : Nat.log n.minFac n = 4
          · left; left; right; exact ⟨hnIcc, hpp, h4⟩
          · by_cases h5 : Nat.log n.minFac n = 5
            · left; right; exact ⟨hnIcc, hpp, h5⟩
            · right; exact ⟨hnIcc, hpp, by omega⟩
    have hnonneg : ∀ n : ℕ, 0 ≤ Real.log (n.minFac : ℝ) := fun n =>
      Real.log_nonneg (by exact_mod_cast Nat.minFac_pos n)
    have hunion_le : ∀ (U V : Finset ℕ),
        ∑ n ∈ U ∪ V, Real.log (n.minFac : ℝ) ≤
          (∑ n ∈ U, Real.log (n.minFac : ℝ)) + ∑ n ∈ V, Real.log (n.minFac : ℝ) := by
      intro U V
      have h1 := Finset.sum_union_inter (s₁ := U) (s₂ := V) (f := fun n : ℕ => Real.log (n.minFac : ℝ))
      have h2 : 0 ≤ ∑ n ∈ U ∩ V, Real.log (n.minFac : ℝ) :=
        Finset.sum_nonneg (fun n _ => hnonneg n)
      linarith
    have hsum_union :
        ∑ n ∈ A.filter IsPrimePow, Real.log (n.minFac : ℝ) ≤
          (∑ n ∈ S2, Real.log (n.minFac : ℝ)) +
          (∑ n ∈ S3, Real.log (n.minFac : ℝ)) +
          (∑ n ∈ S4, Real.log (n.minFac : ℝ)) +
          (∑ n ∈ S5, Real.log (n.minFac : ℝ)) +
          (∑ n ∈ S6, Real.log (n.minFac : ℝ)) := by
      calc ∑ n ∈ A.filter IsPrimePow, Real.log (n.minFac : ℝ)
          ≤ ∑ n ∈ (((S2 ∪ S3) ∪ S4) ∪ S5) ∪ S6, Real.log (n.minFac : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnonneg n)
        _ ≤ (∑ n ∈ ((S2 ∪ S3) ∪ S4) ∪ S5, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S6, Real.log (n.minFac : ℝ) := hunion_le _ _
        _ ≤ ((∑ n ∈ (S2 ∪ S3) ∪ S4, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S5, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S6, Real.log (n.minFac : ℝ) := by gcongr; exact hunion_le _ _
        _ ≤ (((∑ n ∈ S2 ∪ S3, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S4, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S5, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S6, Real.log (n.minFac : ℝ) := by gcongr; exact hunion_le _ _
        _ ≤ ((((∑ n ∈ S2, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S3, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S4, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S5, Real.log (n.minFac : ℝ)) +
              ∑ n ∈ S6, Real.log (n.minFac : ℝ) := by gcongr; exact hunion_le _ _
    have h2 := sum_exact_pow_le hY1 (k := 2) (by omega)
    have h3 := sum_exact_pow_le hY1 (k := 3) (by omega)
    have h4 := sum_exact_pow_le hY1 (k := 4) (by omega)
    have h5 := sum_exact_pow_le hY1 (k := 5) (by omega)
    have h6 := sum_high_pow_le hY1
    linarith
  -- Paso 2: desigualdad numérica para Y ≥ 10^5
  have hlog4 : Real.log 4 ≤ 1.4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he : (2.71828 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
    have h7 : (4 : ℝ) ^ (5 : ℕ) ≤ Real.exp 7 := by
      have : Real.exp 7 = (Real.exp 1) ^ (7 : ℕ) := by
        rw [← Real.exp_natCast_mul]; norm_num
      rw [this]
      calc (4 : ℝ) ^ (5 : ℕ) ≤ (2.71828 : ℝ) ^ (7 : ℕ) := by norm_num
        _ ≤ (Real.exp 1) ^ (7 : ℕ) := by gcongr
    have h5 : (4 : ℝ) ^ (5 : ℕ) ≤ (Real.exp 1.4) ^ (5 : ℕ) := by
      rw [← Real.exp_natCast_mul]
      convert h7 using 2
      norm_num
    by_contra hcon
    push Not at hcon
    have : (Real.exp 1.4) ^ (5 : ℕ) < (4 : ℝ) ^ (5 : ℕ) := by gcongr
    linarith
  have hsqrt_eq : Real.sqrt Y = Y ^ (1 / (2 : ℝ)) := Real.sqrt_eq_rpow Y
  have hY3 : Y ^ (1 / (3 : ℝ)) ≤ 0.147 * Y ^ (1 / (2 : ℝ)) := by
    have hpow : (Y ^ (1 / (3 : ℝ))) ^ (6 : ℕ) ≤ (0.147 * Y ^ (1 / (2 : ℝ))) ^ (6 : ℕ) := by
      rw [mul_pow, ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le,
          ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le]
      norm_num
      nlinarith [sq_nonneg Y]
    by_contra hcon
    push Not at hcon
    have : (0.147 * Y ^ (1 / (2 : ℝ))) ^ (6 : ℕ) < (Y ^ (1 / (3 : ℝ))) ^ (6 : ℕ) := by gcongr
    linarith
  have hY4 : Y ^ (1 / (4 : ℝ)) ≤ 0.0563 * Y ^ (1 / (2 : ℝ)) := by
    have hpow : (Y ^ (1 / (4 : ℝ))) ^ (4 : ℕ) ≤ (0.0563 * Y ^ (1 / (2 : ℝ))) ^ (4 : ℕ) := by
      rw [mul_pow, ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le,
          ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le]
      norm_num
      nlinarith
    by_contra hcon
    push Not at hcon
    have : (0.0563 * Y ^ (1 / (2 : ℝ))) ^ (4 : ℕ) < (Y ^ (1 / (4 : ℝ))) ^ (4 : ℕ) := by gcongr
    linarith
  have hY5 : Y ^ (1 / (5 : ℝ)) ≤ 0.0317 * Y ^ (1 / (2 : ℝ)) := by
    have hpow : (Y ^ (1 / (5 : ℝ))) ^ (10 : ℕ) ≤ (0.0317 * Y ^ (1 / (2 : ℝ))) ^ (10 : ℕ) := by
      rw [mul_pow, ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le,
          ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le]
      norm_num
      have hY3_ge : (10 ^ 5 : ℝ) ^ (3 : ℕ) ≤ Y ^ (3 : ℕ) := by gcongr
      have hsplit : Y ^ (5 : ℕ) = Y ^ (2 : ℕ) * Y ^ (3 : ℕ) := by ring
      rw [hsplit]
      have hcoeff : (1 : ℝ) ≤ (0.0317 : ℝ) ^ (10 : ℕ) * (10 ^ 5 : ℝ) ^ (3 : ℕ) := by norm_num
      nlinarith [sq_nonneg Y]
    by_contra hcon
    push Not at hcon
    have : (0.0317 * Y ^ (1 / (2 : ℝ))) ^ (10 : ℕ) < (Y ^ (1 / (5 : ℝ))) ^ (10 : ℕ) := by gcongr
    linarith
  have hY6log : Y ^ (1 / (6 : ℝ)) * Real.log Y ≤ 0.27 * Y ^ (1 / (2 : ℝ)) := by
    set t := Y ^ (1 / (3 : ℝ))
    have ht0 : 0 < t := by positivity
    have ht46 : 46.4 ≤ t := by
      have hpow : (46.4 : ℝ) ^ (3 : ℕ) ≤ t ^ (3 : ℕ) := by
        dsimp [t]
        rw [← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le]
        norm_num
        linarith
      by_contra hcon
      push Not at hcon
      have : t ^ (3 : ℕ) < (46.4 : ℝ) ^ (3 : ℕ) := by gcongr
      linarith
    have hlogY : Real.log Y = 3 * Real.log t := by
      dsimp [t]
      rw [Real.log_rpow hY0]
      ring
    have hlog46 : Real.log 46.4 ≤ 4 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he : (2.71828 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      have : Real.exp 4 = (Real.exp 1) ^ (4 : ℕ) := by
        rw [← Real.exp_natCast_mul]; norm_num
      rw [this]
      calc (46.4 : ℝ) ≤ (2.71828 : ℝ) ^ (4 : ℕ) := by norm_num
        _ ≤ (Real.exp 1) ^ (4 : ℕ) := by gcongr
    have hlogt : Real.log t ≤ 0.09 * t := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num : (0 : ℝ) < 46.4))
      rw [Real.log_div ht0.ne' (by norm_num)] at h1
      have hdiv_eq : t / 46.4 = (5 / 232 : ℝ) * t := by ring
      rw [hdiv_eq] at h1
      linarith
    have hmul : Y ^ (1 / (6 : ℝ)) * t = Y ^ (1 / (2 : ℝ)) := by
      dsimp [t]
      rw [← Real.rpow_add hY0]
      norm_num
    calc Y ^ (1 / (6 : ℝ)) * Real.log Y
        = Y ^ (1 / (6 : ℝ)) * (3 * Real.log t) := by rw [hlogY]
      _ ≤ Y ^ (1 / (6 : ℝ)) * (0.27 * t) := by
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 0.27 * (Y ^ (1 / (6 : ℝ)) * t) := by ring
      _ = 0.27 * Y ^ (1 / (2 : ℝ)) := by rw [hmul]
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsum_pow :
      (Y ^ (1 / (2 : ℝ)) + Y ^ (1 / (3 : ℝ)) + Y ^ (1 / (4 : ℝ)) + Y ^ (1 / (5 : ℝ))) * Real.log 4
      ≤ 1.729 * Y ^ (1 / (2 : ℝ)) := by
    have h1 : Y ^ (1 / (2 : ℝ)) + Y ^ (1 / (3 : ℝ)) + Y ^ (1 / (4 : ℝ)) + Y ^ (1 / (5 : ℝ))
        ≤ 1.235 * Y ^ (1 / (2 : ℝ)) := by linarith
    have h2 : (Y ^ (1 / (2 : ℝ)) + Y ^ (1 / (3 : ℝ)) + Y ^ (1 / (4 : ℝ)) + Y ^ (1 / (5 : ℝ))) * Real.log 4
        ≤ (1.235 * Y ^ (1 / (2 : ℝ))) * 1.4 :=
      mul_le_mul h1 hlog4 hlog4_nonneg (by positivity)
    linarith
  have hdist :
      Y ^ (1 / (2 : ℝ)) * Real.log 4 + Y ^ (1 / (3 : ℝ)) * Real.log 4 +
      Y ^ (1 / (4 : ℝ)) * Real.log 4 + Y ^ (1 / (5 : ℝ)) * Real.log 4 =
      (Y ^ (1 / (2 : ℝ)) + Y ^ (1 / (3 : ℝ)) + Y ^ (1 / (4 : ℝ)) + Y ^ (1 / (5 : ℝ))) * Real.log 4 := by
    ring
  rw [hsqrt_eq]
  linarith [Real.rpow_nonneg hY0.le (1 / 2 : ℝ)]

/-! ### Conteo de ceros no triviales `N(T)` y simetría de `sinc²` (sin `sorry`) -/

/-- Función `sinc²(u) = (sin u / u)²`. -/
noncomputable def sincSq (u : ℝ) : ℝ :=
  (Real.sin u / u) ^ 2

lemma sincSq_nonneg (u : ℝ) : 0 ≤ sincSq u := sq_nonneg _

lemma sincSq_even (u : ℝ) : sincSq (-u) = sincSq u := by
  unfold sincSq
  rw [Real.sin_neg, neg_div_neg_eq]

lemma sincSq_zero : sincSq 0 = 0 := by
  simp [sincSq]

lemma sincSq_le_one (u : ℝ) : sincSq u ≤ 1 := by
  unfold sincSq
  by_cases hu : u = 0
  · subst hu; simp
  · have hsin : |Real.sin u| ≤ |u| := Real.abs_sin_le_abs
    have hdiv : |Real.sin u / u| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr hu)]
      exact hsin
    rw [← sq_abs]
    nlinarith [abs_nonneg (Real.sin u / u)]

lemma sincSq_le_inv_sq {u : ℝ} (_hu : u ≠ 0) : sincSq u ≤ 1 / u ^ 2 := by
  unfold sincSq
  rw [div_pow, one_div]
  have hsin : Real.sin u ^ 2 ≤ 1 := by
    have := Real.sin_sq_le_one u
    exact this
  calc Real.sin u ^ 2 / u ^ 2 ≤ 1 / u ^ 2 :=
        div_le_div_of_nonneg_right hsin (sq_nonneg u)
    _ = (u ^ 2)⁻¹ := one_div _

/-- Todo cero no trivial de `ζ(s)` cumple `Re(ρ) < 1`. -/
lemma nontrivialZero_re_lt_one {ρ : ℂ} (hρ : IsNontrivialZero ρ) : ρ.re < 1 := by
  by_contra h
  push Not at h
  exact riemannZeta_ne_zero_of_one_le_re h hρ.1

/-- Todo cero no trivial de `ζ(s)` cumple `0 < Re(ρ)`. -/
lemma nontrivialZero_re_pos {ρ : ℂ} (hρ : IsNontrivialZero ρ) : 0 < ρ.re := by
  by_contra h
  push Not at h
  have hne0 : ρ ≠ 0 := by
    intro h0
    have hz := hρ.1
    rw [h0, riemannZeta_zero] at hz
    norm_num at hz
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hgamma_ne : ρ.Gammaℝ ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    apply mul_ne_zero
    · rw [Complex.cpow_def_of_ne_zero hpi_ne]
      exact Complex.exp_ne_zero _
    · apply Complex.Gamma_ne_zero
      intro m hm
      by_cases hm0 : m = 0
      · subst hm0
        simp only [Nat.cast_zero, neg_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] at hm
        exact hne0 hm
      · apply hρ.2.1
        refine ⟨m - 1, ?_⟩
        have hm1 : (m : ℂ) = ((m - 1 : ℕ) : ℂ) + 1 := by
          norm_cast; omega
        have hρ_eq : ρ = -2 * (m : ℂ) := by linear_combination 2 * hm
        rw [hρ_eq, hm1]
  have hcomp_zero : completedRiemannZeta ρ = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hne0
    rw [hρ.1] at hdef
    exact (div_eq_zero_iff.mp hdef.symm).resolve_right hgamma_ne
  have h1sub : completedRiemannZeta (1 - ρ) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hcomp_zero
  have hre1 : 1 ≤ (1 - ρ).re := by simp; linarith
  have h1sub_ne0 : (1 - ρ) ≠ 0 := by
    intro h0
    have h0re : (1 - ρ).re = 0 := by rw [h0]; simp
    linarith
  have hzeta1 : riemannZeta (1 - ρ) = 0 := by
    rw [riemannZeta_def_of_ne_zero h1sub_ne0, h1sub, zero_div]
  exact riemannZeta_ne_zero_of_one_le_re hre1 hzeta1

/-- La conjugación compleja preserva los ceros no triviales de `ζ(s)`. -/
lemma IsNontrivialZero.conj {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    IsNontrivialZero (starRingEnd ℂ ρ) := by
  have hne0 : ρ ≠ 0 := by
    intro h0
    have hz := hρ.1
    rw [h0, riemannZeta_zero] at hz
    norm_num at hz
  have hconj_ne0 : starRingEnd ℂ ρ ≠ 0 := by simpa using hne0
  have hzeta : riemannZeta (starRingEnd ℂ ρ) = 0 := by
    rw [riemannZeta_def_of_ne_zero hconj_ne0, completedRiemannZeta_conj, Complex.Gammaℝ_conj,
        ← map_div₀, ← riemannZeta_def_of_ne_zero hne0, hρ.1, _root_.map_zero]
  refine ⟨hzeta, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    apply hρ.2.1
    refine ⟨n, ?_⟩
    have h1 := congrArg (starRingEnd ℂ) hn
    simpa [map_ofNat] using h1
  · intro h1
    apply hρ.2.2
    have := congrArg (starRingEnd ℂ) h1
    simpa using this

/-- Conjunto de ceros no triviales de `ζ` en el semiplano superior hasta altura `T`. -/
def nontrivialZerosUpTo (T : ℝ) : Set ℂ :=
  {ρ : ℂ | IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- Para todo `T : ℝ`, el conjunto de ceros no triviales con `0 < Im(ρ) ≤ T` es finito. -/
lemma nontrivialZerosUpTo_finite (T : ℝ) : (nontrivialZerosUpTo T).Finite := by
  have hsub : nontrivialZerosUpTo T ⊆
      Metric.closedBall (0 : ℂ) (1 + |T|) ∩ riemannZetaZeros := by
    intro ρ hρ
    refine ⟨?_, hρ.1.1⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre1 : ρ.re < 1 := nontrivialZero_re_lt_one hρ.1
    have hre0 : 0 < ρ.re := nontrivialZero_re_pos hρ.1
    have hre_abs : |ρ.re| ≤ 1 := by rw [abs_of_pos hre0]; linarith
    have him_abs : |ρ.im| ≤ |T| := by
      rw [abs_of_pos hρ.2.1]
      exact le_trans hρ.2.2 (le_abs_self T)
    calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + |T| := add_le_add hre_abs him_abs
  exact (isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_riemannZetaZeros_finite.subset hsub

/-- Función de conteo de ceros no triviales `N(T) = #{ρ : ζ(ρ) = 0, 0 < Im(ρ) ≤ T}`. -/
noncomputable def zeroCount (T : ℝ) : ℕ :=
  (nontrivialZerosUpTo T).ncard

lemma zeroCount_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : zeroCount T₁ ≤ zeroCount T₂ :=
  Set.ncard_le_ncard (fun _ hρ => ⟨hρ.1, hρ.2.1, le_trans hρ.2.2 h⟩) (nontrivialZerosUpTo_finite T₂)

lemma zeroCount_eq_zero_of_nonpos {T : ℝ} (hT : T ≤ 0) : zeroCount T = 0 := by
  unfold zeroCount
  have hempty : nontrivialZerosUpTo T = ∅ := by
    ext ρ
    simp only [nontrivialZerosUpTo, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, hpos, hle⟩
    linarith
  rw [hempty, Set.ncard_empty]

lemma summable_sum_elim {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    (hf : Summable f) (hg : Summable g) : Summable (Sum.elim f g) := by
  have hf' : Summable (Sum.elim f (0 : β → ℝ)) := by
    rw [← Function.Injective.summable_iff Sum.inl_injective]
    · exact hf
    · rintro (a | b) h
      · exact absurd ⟨a, rfl⟩ h
      · rfl
  have hg' : Summable (Sum.elim (0 : α → ℝ) g) := by
    rw [← Function.Injective.summable_iff Sum.inr_injective]
    · exact hg
    · rintro (a | b) h
      · rfl
      · exact absurd ⟨b, rfl⟩ h
  have heq : Sum.elim f g = (fun x => Sum.elim f (0 : β → ℝ) x + Sum.elim (0 : α → ℝ) g x) := by
    ext (a | b) <;> simp
  rw [heq]
  exact hf'.add hg'

lemma tsum_sum_elim {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    (hf : Summable f) (hg : Summable g) :
    (∑' x : α ⊕ β, Sum.elim f g x) = (∑' a : α, f a) + (∑' b : β, g b) := by
  have hf' : Summable (Sum.elim f (0 : β → ℝ)) := by
    rw [← Function.Injective.summable_iff Sum.inl_injective]
    · exact hf
    · rintro (a | b) h
      · exact absurd ⟨a, rfl⟩ h
      · rfl
  have hg' : Summable (Sum.elim (0 : α → ℝ) g) := by
    rw [← Function.Injective.summable_iff Sum.inr_injective]
    · exact hg
    · rintro (a | b) h
      · rfl
      · exact absurd ⟨b, rfl⟩ h
  have heq : Sum.elim f g = (fun x => Sum.elim f (0 : β → ℝ) x + Sum.elim (0 : α → ℝ) g x) := by
    ext (a | b) <;> simp
  rw [heq, hf'.tsum_add hg']
  congr 1
  · refine (Function.Injective.tsum_eq Sum.inl_injective ?_).symm
    rintro (a | b) h
    · exact ⟨a, rfl⟩
    · exact absurd rfl h
  · refine (Function.Injective.tsum_eq Sum.inr_injective ?_).symm
    rintro (a | b) h
    · exact absurd rfl h
    · exact ⟨b, rfl⟩

/-- Simetría de la suma de `sinc²`: la suma sobre todos los ceros no triviales es el doble
    de la suma sobre los ceros con parte imaginaria positiva. -/
lemma tsum_nontrivialZeros_eq_two_mul_pos (h : ℝ)
    (hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZero ρ ∧ 0 < ρ.im} =>
      sincSq (ρ.1.im * h / 2))) :
    (∑' ρ : {ρ : ℂ // IsNontrivialZero ρ}, sincSq (ρ.1.im * h / 2)) =
      2 * (∑' ρ : {ρ : ℂ // IsNontrivialZero ρ ∧ 0 < ρ.im}, sincSq (ρ.1.im * h / 2)) := by
  set Pos := {ρ : ℂ // IsNontrivialZero ρ ∧ 0 < ρ.im}
  set Neg := {ρ : ℂ // IsNontrivialZero ρ ∧ ρ.im < 0}
  let eNeg : Pos ≃ Neg :=
    { toFun := fun ρ => ⟨starRingEnd ℂ ρ.1, ρ.2.1.conj, by simp [ρ.2.2]⟩
      invFun := fun ρ => ⟨starRingEnd ℂ ρ.1, ρ.2.1.conj, by simp [ρ.2.2]⟩
      left_inv := fun ⟨ρ, _⟩ => by ext; simp
      right_inv := fun ⟨ρ, _⟩ => by ext; simp }
  have hsum_neg : Summable (fun ρ : Neg => sincSq (ρ.1.im * h / 2)) := by
    refine (Equiv.summable_iff eNeg (f := fun ρ : Neg => sincSq (ρ.1.im * h / 2))).mp ?_
    have hcomp : ((fun ρ : Neg => sincSq (ρ.1.im * h / 2)) ∘ eNeg) =
        (fun ρ : Pos => sincSq (ρ.1.im * h / 2)) := by
      ext ρ
      simp only [Function.comp_apply, eNeg, Equiv.coe_fn_mk, Complex.conj_im, neg_mul, neg_div,
        sincSq_even]
    rw [hcomp]
    exact hsum
  have htsum_neg :
      (∑' ρ : Neg, sincSq (ρ.1.im * h / 2)) = ∑' ρ : Pos, sincSq (ρ.1.im * h / 2) := by
    rw [← Equiv.tsum_eq eNeg (fun ρ : Neg => sincSq (ρ.1.im * h / 2))]
    refine tsum_congr (fun ρ => ?_)
    simp only [eNeg, Equiv.coe_fn_mk, Complex.conj_im, neg_mul, neg_div, sincSq_even]
  let ZeroIm := {ρ : ℂ // IsNontrivialZero ρ ∧ ρ.im = 0}
  let eAll : {ρ : ℂ // IsNontrivialZero ρ} ≃ (Pos ⊕ Neg) ⊕ ZeroIm :=
    { toFun := fun ⟨ρ, hρ⟩ =>
        if hpos : 0 < ρ.im then Sum.inl (Sum.inl ⟨ρ, hρ, hpos⟩)
        else if hneg : ρ.im < 0 then Sum.inl (Sum.inr ⟨ρ, hρ, hneg⟩)
        else Sum.inr ⟨ρ, hρ, by linarith⟩
      invFun := fun s => match s with
        | Sum.inl (Sum.inl ⟨ρ, hρ, _⟩) => ⟨ρ, hρ⟩
        | Sum.inl (Sum.inr ⟨ρ, hρ, _⟩) => ⟨ρ, hρ⟩
        | Sum.inr ⟨ρ, hρ, _⟩ => ⟨ρ, hρ⟩
      left_inv := fun ⟨ρ, hρ⟩ => by
        by_cases hpos : 0 < ρ.im
        · simp [hpos]
        · by_cases hneg : ρ.im < 0
          · simp [hpos, hneg]
          · simp [hpos, hneg]
      right_inv := fun s => by
        rcases s with (⟨ρ, hρ, hpos⟩ | ⟨ρ, hρ, hneg⟩) | ⟨ρ, hρ, h0⟩
        · simp [hpos]
        · have hnotpos : ¬ (0 < ρ.im) := by linarith
          simp [hnotpos, hneg]
        · simp [h0] }
  have hsum_zero : Summable (fun ρ : ZeroIm => sincSq (ρ.1.im * h / 2)) := by
    have : (fun ρ : ZeroIm => sincSq (ρ.1.im * h / 2)) = fun _ => 0 := by
      ext ⟨ρ, _, h0⟩
      simp [h0, sincSq_zero]
    rw [this]
    exact summable_zero
  have htsum_zero : (∑' ρ : ZeroIm, sincSq (ρ.1.im * h / 2)) = 0 := by
    have : (fun ρ : ZeroIm => sincSq (ρ.1.im * h / 2)) = fun _ => 0 := by
      ext ⟨ρ, _, h0⟩
      simp [h0, sincSq_zero]
    rw [this, tsum_zero]
  let fAll : {ρ : ℂ // IsNontrivialZero ρ} → ℝ := fun ρ => sincSq (ρ.1.im * h / 2)
  have hfeq : (fun s : (Pos ⊕ Neg) ⊕ ZeroIm => fAll (eAll.symm s)) =
      Sum.elim (Sum.elim (fun ρ : Pos => sincSq (ρ.1.im * h / 2))
                         (fun ρ : Neg => sincSq (ρ.1.im * h / 2)))
               (fun ρ : ZeroIm => sincSq (ρ.1.im * h / 2)) := by
    ext s
    rcases s with (⟨ρ, hρ, hpos⟩ | ⟨ρ, hρ, hneg⟩) | ⟨ρ, hρ, h0⟩ <;> rfl
  have hsum_pn : Summable (Sum.elim (fun ρ : Pos => sincSq (ρ.1.im * h / 2))
                                    (fun ρ : Neg => sincSq (ρ.1.im * h / 2))) :=
    summable_sum_elim hsum hsum_neg
  change ∑' ρ, fAll ρ = 2 * ∑' ρ : Pos, sincSq (ρ.1.im * h / 2)
  rw [← Equiv.tsum_eq eAll.symm fAll, hfeq]
  rw [tsum_sum_elim hsum_pn hsum_zero, tsum_sum_elim hsum hsum_neg]
  rw [htsum_neg, htsum_zero]
  ring

/-! ### Las cajas analíticas clásicas (Fórmula explícita de Weil y Riemann–von Mangoldt) -/

lemma weil_explicit_formula_triWeight {x : ℝ} (hx : 10^5 ≤ x) :
    let Δ := Real.sqrt x * Real.log x
    (mellinTriWeight x Δ 1).re
      - ∑' ρ : {ρ : ℂ // IsNontrivialZero ρ}, ‖mellinTriWeight x Δ ρ.1‖
      - 0.01
    ≤ weightedVonMangoldt x Δ := by
  sorry

/-- Cota explícita de Riemann–von Mangoldt (Trudgian, 2014):
    no hay ceros no triviales con `0 < Im(ρ) ≤ 14` y para `T ≥ e`,
    `|N(T) - (T / (2π)) ln(T / (2πe))| ≤ 0.112 ln T + 0.278 ln(ln T) + 2.51`. -/
lemma riemann_von_mangoldt_trudgian :
    zeroCount 14 = 0 ∧
    ∀ T : ℝ, Real.exp 1 ≤ T →
      |(zeroCount T : ℝ) - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.51 := by
  sorry

/-- De la cota de Trudgian se deduce que cada banda unitaria `(n, n + 1]` (`n ≥ 14`)
    contiene a lo sumo `21 * √n` ceros no triviales. -/
lemma zeroCount_step_le_of_rvm
    (hRvM : ∀ T : ℝ, Real.exp 1 ≤ T →
      |(zeroCount T : ℝ) - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.51)
    {n : ℕ} (hn : 14 ≤ n) :
    ((zeroCount (n + 1 : ℕ) - zeroCount (n : ℕ) : ℕ) : ℝ) ≤ 21 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hnR : (14 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn10 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have he14 : Real.exp 1 ≤ (n : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he15 : Real.exp 1 ≤ (n : ℝ) + 1 := by linarith
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have h2pie_gt1 : (1 : ℝ) < 2 * Real.pi * Real.exp 1 := by
    have : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    nlinarith
  have hmono : zeroCount (n : ℕ) ≤ zeroCount (n + 1 : ℕ) :=
    zeroCount_mono (by exact_mod_cast Nat.le_succ n)
  rw [Nat.cast_sub hmono]
  have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hR1 := hRvM ((n : ℝ) + 1) he15
  have hR0 := hRvM (n : ℝ) he14
  rw [abs_le] at hR1 hR0
  -- Cota sobre el incremento del término principal
  have hlog_inc : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    rw [← Real.log_div hn10.ne' hn0.ne']
    have hdiv : ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by field_simp
    rw [hdiv]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (n : ℝ) by positivity)
    linarith
  have hlog_n1_ge1 : (1 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le hn10]; exact he15
  have hlog_n_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hn0]; exact he14
  have hlog_mono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hn0 (by linarith)
  have hmain_diff :
      (((n : ℝ) + 1) / (2 * Real.pi)) * Real.log (((n : ℝ) + 1) / (2 * Real.pi * Real.exp 1)) -
      ((n : ℝ) / (2 * Real.pi)) * Real.log ((n : ℝ) / (2 * Real.pi * Real.exp 1)) ≤
      Real.log ((n : ℝ) + 1) := by
    have h2pie_ne : (2 * Real.pi * Real.exp 1 : ℝ) ≠ 0 := by positivity
    rw [Real.log_div hn10.ne' h2pie_ne, Real.log_div hn0.ne' h2pie_ne]
    have hlog2pie : 0 ≤ Real.log (2 * Real.pi * Real.exp 1) :=
      Real.log_nonneg h2pie_gt1.le
    have halg :
        (((n : ℝ) + 1) / (2 * Real.pi)) * (Real.log ((n : ℝ) + 1) - Real.log (2 * Real.pi * Real.exp 1)) -
        ((n : ℝ) / (2 * Real.pi)) * (Real.log (n : ℝ) - Real.log (2 * Real.pi * Real.exp 1)) =
        (Real.log ((n : ℝ) + 1) + (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) -
          Real.log (2 * Real.pi * Real.exp 1)) / (2 * Real.pi) := by
      field_simp; ring
    rw [halg, div_le_iff₀ h2pi_pos]
    have hn_mul : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 := by
      calc (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
          ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hlog_inc hn0.le
        _ = 1 := by field_simp
    nlinarith
  have herr1 : 0.112 * Real.log ((n : ℝ) + 1) + 0.278 * Real.log (Real.log ((n : ℝ) + 1)) + 2.51 ≤
      3 * Real.log ((n : ℝ) + 1) := by
    have hll : Real.log (Real.log ((n : ℝ) + 1)) ≤ Real.log ((n : ℝ) + 1) := by
      have := Real.log_le_sub_one_of_pos (show 0 < Real.log ((n : ℝ) + 1) by linarith)
      linarith
    linarith
  have herr0 : 0.112 * Real.log (n : ℝ) + 0.278 * Real.log (Real.log (n : ℝ)) + 2.51 ≤
      3 * Real.log ((n : ℝ) + 1) := by
    have hll : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show 0 < Real.log (n : ℝ) by linarith)
      linarith
    linarith
  have hdiff_log : (zeroCount (n + 1 : ℕ) : ℝ) - (zeroCount (n : ℕ) : ℝ) ≤
      7 * Real.log ((n : ℝ) + 1) := by
    rw [hcast1]
    linarith
  -- Finalmente, ln(n + 1) ≤ 3 * n^(1/2)
  have hlog_le_sqrt : Real.log ((n : ℝ) + 1) ≤ 3 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hle2n : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have hsqrt_eq : (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow _).symm
    rw [hsqrt_eq]
    have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hn10 hle2n
    have h2 : Real.log (2 * (n : ℝ)) = Real.log 2 + 2 * Real.log (Real.sqrt (n : ℝ)) := by
      rw [Real.log_mul (by norm_num) hn0.ne', Real.log_sqrt hn0.le]; ring
    have h3 : Real.log (Real.sqrt (n : ℝ)) ≤ Real.sqrt (n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn0)
    have hlog2 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
    have hsqrt_pos : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    linarith
  linarith

/-- Sumabilidad de `sinc²(γh/2)` sobre los ceros no triviales con `Im(ρ) > 0`,
    demostrada sin `sorry` a partir de la cota de Riemann–von Mangoldt (Trudgian). -/
lemma pos_zero_sum_sinc_sq_summable {h : ℝ} (hh0 : 0 < h)
    (hRvM : zeroCount 14 = 0 ∧
      ∀ T : ℝ, Real.exp 1 ≤ T →
        |(zeroCount T : ℝ) - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
          0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.51) :
    Summable (fun ρ : {ρ : ℂ // IsNontrivialZero ρ ∧ 0 < ρ.im} => sincSq (ρ.1.im * h / 2)) := by
  set Pos := {ρ : ℂ // IsNontrivialZero ρ ∧ 0 < ρ.im}
  have h14 : ∀ ρ : Pos, (14 : ℝ) < ρ.1.im := by
    intro ρ
    by_contra hle
    push Not at hle
    have hmem : ρ.1 ∈ nontrivialZerosUpTo 14 := ⟨ρ.2.1, ρ.2.2, hle⟩
    have hpos : 0 < zeroCount 14 :=
      Set.ncard_pos (nontrivialZerosUpTo_finite 14) |>.mpr ⟨ρ.1, hmem⟩
    omega
  have hbase_summable : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hC_summable : Summable (fun n : ℕ => (84 / h ^ 2) * ((1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ))) :=
    hbase_summable.mul_left (84 / h ^ 2)
  refine summable_of_sum_le (fun ρ => sincSq_nonneg _) (c := ∑' n : ℕ, (84 / h ^ 2) * ((1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ))) ?_
  intro s
  let M : ℕ := s.sup (fun ρ => Nat.ceil ρ.1.im)
  have hband_maps : ∀ ρ ∈ s, Nat.ceil ρ.1.im - 1 ∈ Finset.Ico 14 M := by
    intro ρ hρ
    rw [Finset.mem_Ico]
    have hlt14 : (14 : ℝ) < ρ.1.im := h14 ρ
    have hceil15 : 15 ≤ Nat.ceil ρ.1.im := by
      have : (14 : ℕ) < Nat.ceil ρ.1.im := Nat.lt_ceil.mpr (by exact_mod_cast hlt14)
      omega
    have hleM : Nat.ceil ρ.1.im ≤ M := Finset.le_sup (f := fun ρ : Pos => Nat.ceil ρ.1.im) hρ
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hband_maps]
  have hfiber_le : ∀ n ∈ Finset.Ico 14 M,
      ∑ ρ ∈ s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n), sincSq (ρ.1.im * h / 2) ≤
        (84 / h ^ 2) * ((1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn14 : 14 ≤ n := hn.1
    have hnR : (14 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn14
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    -- Cada término en la fibra cumple n < ρ.im ≤ n + 1, luego sincSq(ρ.im * h / 2) ≤ 4 / (h^2 * n^2)
    have hterm : ∀ ρ ∈ s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n),
        sincSq (ρ.1.im * h / 2) ≤ 4 / (h ^ 2 * (n : ℝ) ^ 2) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hceil_eq : Nat.ceil ρ.1.im = n + 1 := by
        have hlt14 : (14 : ℝ) < ρ.1.im := h14 ρ
        have : (14 : ℕ) < Nat.ceil ρ.1.im := Nat.lt_ceil.mpr (by exact_mod_cast hlt14)
        omega
      have hn_lt : (n : ℝ) < ρ.1.im := by
        have hlt : n < Nat.ceil ρ.1.im := by omega
        exact Nat.lt_ceil.mp hlt
      have hρpos : 0 < ρ.1.im := ρ.2.2
      have hu_pos : 0 < ρ.1.im * h / 2 := by positivity
      calc sincSq (ρ.1.im * h / 2)
          ≤ 1 / (ρ.1.im * h / 2) ^ 2 := sincSq_le_inv_sq hu_pos.ne'
        _ = 4 / (h ^ 2 * ρ.1.im ^ 2) := by field_simp; ring
        _ ≤ 4 / (h ^ 2 * (n : ℝ) ^ 2) := by gcongr
    -- La cardinalidad de la fibra es ≤ zeroCount (n + 1) - zeroCount n
    have hcard :
        (s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n)).card ≤
          zeroCount (n + 1 : ℕ) - zeroCount (n : ℕ) := by
      have himg_sub :
          ((s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n)).image Subtype.val : Set ℂ) ⊆
            nontrivialZerosUpTo (n + 1 : ℕ) \ nontrivialZerosUpTo (n : ℕ) := by
        intro z hz
        rw [Finset.coe_image, Set.mem_image] at hz
        rcases hz with ⟨ρ, hρ, rfl⟩
        rw [Finset.mem_coe, Finset.mem_filter] at hρ
        have hceil_eq : Nat.ceil ρ.1.im = n + 1 := by
          have hlt14 : (14 : ℝ) < ρ.1.im := h14 ρ
          have : (14 : ℕ) < Nat.ceil ρ.1.im := Nat.lt_ceil.mpr (by exact_mod_cast hlt14)
          omega
        have hn_lt : (n : ℝ) < ρ.1.im := Nat.lt_ceil.mp (by omega)
        have hn1_ge : ρ.1.im ≤ ((n + 1 : ℕ) : ℝ) := by
          rw [← hceil_eq]; exact Nat.le_ceil ρ.1.im
        refine ⟨⟨ρ.2.1, ρ.2.2, hn1_ge⟩, ?_⟩
        intro hmem
        linarith [hmem.2.2]
      have hcard_eq :
          (s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n)).card =
            (((s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n)).image Subtype.val : Set ℂ)).ncard := by
        rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ Subtype.val_injective]
      rw [hcard_eq]
      have hfin_diff : (nontrivialZerosUpTo (n + 1 : ℕ) \ nontrivialZerosUpTo (n : ℕ)).Finite :=
        (nontrivialZerosUpTo_finite (n + 1 : ℕ)).sdiff
      have hsub_n : nontrivialZerosUpTo (n : ℕ) ⊆ nontrivialZerosUpTo (n + 1 : ℕ) :=
        fun _ hρ => ⟨hρ.1, hρ.2.1, le_trans hρ.2.2 (by exact_mod_cast Nat.le_succ n)⟩
      have hdiff_eq :
          (nontrivialZerosUpTo (n + 1 : ℕ) \ nontrivialZerosUpTo (n : ℕ)).ncard =
            (nontrivialZerosUpTo (n + 1 : ℕ)).ncard - (nontrivialZerosUpTo (n : ℕ)).ncard :=
        Set.ncard_sdiff' hsub_n (nontrivialZerosUpTo_finite (n + 1 : ℕ))
      exact (Set.ncard_le_ncard himg_sub hfin_diff).trans_eq hdiff_eq
    have hstep := zeroCount_step_le_of_rvm hRvM.2 hn14
    have hrpow_split : (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 = 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
      have hsq : (n : ℝ) ^ (2 : ℕ) = (n : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      rw [hsq, div_eq_div_iff (Real.rpow_pos_of_pos hn0 _).ne' (Real.rpow_pos_of_pos hn0 _).ne']
      rw [one_mul, ← Real.rpow_add hn0]
      norm_num
    calc ∑ ρ ∈ s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n), sincSq (ρ.1.im * h / 2)
        ≤ ∑ _ρ ∈ s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n), (4 / (h ^ 2 * (n : ℝ) ^ 2)) :=
          Finset.sum_le_sum hterm
      _ = ((s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n)).card : ℝ) * (4 / (h ^ 2 * (n : ℝ) ^ 2)) := by
          simp
      _ ≤ ((zeroCount (n + 1 : ℕ) - zeroCount (n : ℕ) : ℕ) : ℝ) * (4 / (h ^ 2 * (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ ≤ (21 * (n : ℝ) ^ (1 / 2 : ℝ)) * (4 / (h ^ 2 * (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (84 / h ^ 2) * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by ring
      _ = (84 / h ^ 2) * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by rw [hrpow_split]
  calc ∑ n ∈ Finset.Ico 14 M,
          ∑ ρ ∈ s.filter (fun ρ => Nat.ceil ρ.1.im - 1 = n), sincSq (ρ.1.im * h / 2)
      ≤ ∑ n ∈ Finset.Ico 14 M, (84 / h ^ 2) * ((1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) :=
        Finset.sum_le_sum hfiber_le
    _ ≤ ∑' n : ℕ, (84 / h ^ 2) * ((1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) :=
        hC_summable.sum_le_tsum (Finset.Ico 14 M) (fun n _ => by positivity)

/-! ### Sumación por partes de Abel–Stieltjes sobre los ceros no triviales (sin `sorry`) -/

/-- Término principal de Riemann–von Mangoldt: `M(t) = (t / (2π)) ln(t / (2πe))`. -/
noncomputable def rvmMainTerm (t : ℝ) : ℝ :=
  (t / (2 * Real.pi)) * Real.log (t / (2 * Real.pi * Real.exp 1))

/-- Derivada exacta del término principal: `M'(t) = (1 / (2π)) ln(t / (2π))` para `t > 0`. -/
lemma rvmMainTerm_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt rvmMainTerm ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) t := by
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h2pie_ne : (2 * Real.pi * Real.exp 1 : ℝ) ≠ 0 := by positivity
  have hdiv_ne : t / (2 * Real.pi * Real.exp 1) ≠ 0 := div_ne_zero ht.ne' h2pie_ne
  have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) t :=
    (hasDerivAt_id t).div_const (2 * Real.pi)
  have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi * Real.exp 1)))
      ((1 / (2 * Real.pi * Real.exp 1)) / (t / (2 * Real.pi * Real.exp 1))) t := by
    have hin : HasDerivAt (fun x : ℝ => x / (2 * Real.pi * Real.exp 1))
        (1 / (2 * Real.pi * Real.exp 1)) t :=
      (hasDerivAt_id t).div_const (2 * Real.pi * Real.exp 1)
    exact hin.log hdiv_ne
  have hmul : HasDerivAt rvmMainTerm
      ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi * Real.exp 1)) +
       (t / (2 * Real.pi)) * ((1 / (2 * Real.pi * Real.exp 1)) / (t / (2 * Real.pi * Real.exp 1)))) t :=
    h1.mul h2
  convert hmul using 1
  have hlog_split :
      Real.log (t / (2 * Real.pi * Real.exp 1)) = Real.log (t / (2 * Real.pi)) - 1 := by
    rw [show t / (2 * Real.pi * Real.exp 1) = (t / (2 * Real.pi)) / Real.exp 1 by ring,
        Real.log_div (div_ne_zero ht.ne' h2pi_ne) (Real.exp_ne_zero 1), Real.log_exp]
  rw [hlog_split]
  have hsimp : (1 / (2 * Real.pi * Real.exp 1)) / (t / (2 * Real.pi * Real.exp 1)) = 1 / t := by
    field_simp
  rw [hsimp]
  field_simp
  ring

/-- `M(14) < 0` porque `14 < 2πe`. -/
lemma rvmMainTerm_14_neg : rvmMainTerm 14 < 0 := by
  unfold rvmMainTerm
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2pie : (14 : ℝ) < 2 * Real.pi * Real.exp 1 := by nlinarith
  have hdiv_lt : (14 : ℝ) / (2 * Real.pi * Real.exp 1) < 1 := by
    rw [div_lt_one (by positivity)]; exact h2pie
  have hlog_neg : Real.log (14 / (2 * Real.pi * Real.exp 1)) < 0 :=
    Real.log_neg (by positivity) hdiv_lt
  exact mul_neg_of_pos_of_neg (by positivity) hlog_neg

/-- Fórmula exacta de sumación por partes de Abel–Stieltjes sobre `nontrivialZerosUpTo T`:
    `∑_{0 < Im(ρ) ≤ T} f(Im(ρ)) = N(T) f(T) - ∫_{14}^T N(t) f'(t) dt`. -/
lemma abel_summation_zeros {T : ℝ} (hT : 14 ≤ T) (h0 : zeroCount 14 = 0)
    {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (14 : ℝ) T, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc (14 : ℝ) T)) :
    ∑ ρ ∈ (nontrivialZerosUpTo_finite T).toFinset, f ρ.im =
      (zeroCount T : ℝ) * f T - ∫ t in (14 : ℝ)..T, (zeroCount t : ℝ) * f' t := by
  set A := (nontrivialZerosUpTo_finite T).toFinset
  have hA_card : (A.card : ℝ) = (zeroCount T : ℝ) := by
    unfold zeroCount
    rw [← Set.ncard_coe_finset A]
    simp [A]
  have h14_lt : ∀ ρ ∈ A, (14 : ℝ) < ρ.im := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    by_contra hle
    push Not at hle
    have hmem : ρ ∈ nontrivialZerosUpTo 14 := ⟨hρ.1, hρ.2.1, hle⟩
    have hpos : 0 < zeroCount 14 :=
      (Set.ncard_pos (nontrivialZerosUpTo_finite 14)).mpr ⟨ρ, hmem⟩
    omega
  have hle_T : ∀ ρ ∈ A, ρ.im ≤ T := fun ρ hρ => ((Set.Finite.mem_toFinset _).mp hρ).2.2
  -- Representación de N(t) como suma de indicatrices en [14, T]
  have hN_eq : ∀ t ∈ Set.Icc (14 : ℝ) T,
      (zeroCount t : ℝ) = ∑ ρ ∈ A, Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t := by
    intro t ht
    have hsub : nontrivialZerosUpTo t ⊆ nontrivialZerosUpTo T :=
      fun _ hρ => ⟨hρ.1, hρ.2.1, le_trans hρ.2.2 ht.2⟩
    have hfilt : (A.filter (fun ρ => ρ.im ≤ t) : Set ℂ) = nontrivialZerosUpTo t := by
      ext ρ
      simp only [A, Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨hρT, hρt⟩; exact ⟨hρT.1, hρT.2.1, hρt⟩
      · intro hρt; exact ⟨hsub hρt, hρt.2.2⟩
    have hcard : zeroCount t = (A.filter (fun ρ => ρ.im ≤ t)).card := by
      unfold zeroCount
      rw [← hfilt, Set.ncard_coe_finset]
    rw [hcard, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hle : ρ.im ≤ t
    · simp [Set.indicator, Set.mem_Ici, hle]
    · simp [Set.indicator, Set.mem_Ici, hle]
  -- Integral de cada indicatriz multiplicada por f'
  have hint_piece : ∀ ρ ∈ A,
      IntervalIntegrable (fun t => Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t)
        MeasureTheory.volume 14 T ∧
      (∫ t in (14 : ℝ)..T, Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t) =
        f T - f ρ.im := by
    intro ρ hρ
    have h14ρ : (14 : ℝ) < ρ.im := h14_lt ρ hρ
    have hρT : ρ.im ≤ T := hle_T ρ hρ
    have hint_f' : IntervalIntegrable f' MeasureTheory.volume 14 T :=
      hf'.intervalIntegrable_of_Icc hT
    have heq_ind : (fun t => Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t) =
        Set.indicator (Set.Ici ρ.im) f' := by
      ext t
      by_cases ht : ρ.im ≤ t <;> simp [Set.indicator, Set.mem_Ici, ht]
    rw [heq_ind]
    have hint_ind : IntervalIntegrable (Set.indicator (Set.Ici ρ.im) f') MeasureTheory.volume 14 T := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
      exact (hint_f'.1).indicator measurableSet_Ici
    refine ⟨hint_ind, ?_⟩
    rw [intervalIntegral.integral_of_le hT,
        MeasureTheory.integral_indicator measurableSet_Ici,
        MeasureTheory.Measure.restrict_restrict measurableSet_Ici]
    have hinter' : Set.Ici ρ.im ∩ Set.Ioc 14 T = Set.Icc ρ.im T := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
    rw [hinter', MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hρT]
    have hsub_icc : Set.Icc ρ.im T ⊆ Set.Icc 14 T := fun t ht => ⟨by linarith [ht.1], ht.2⟩
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hf t (hsub_icc (by rwa [Set.uIcc_of_le hρT] at ht)))
      ((hf'.mono hsub_icc).intervalIntegrable_of_Icc hρT)
  -- Combinamos con Fubini finito sobre A
  have hint_eq :
      (∫ t in (14 : ℝ)..T, (zeroCount t : ℝ) * f' t) =
        ∫ t in (14 : ℝ)..T, ∑ ρ ∈ A, Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    dsimp only
    rw [hN_eq t ht, Finset.sum_mul]
  have hint_sum :
      ∀ s : Finset ℂ,
        (∀ ρ ∈ s, IntervalIntegrable
          (fun t => Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t)
          MeasureTheory.volume 14 T) →
        (∫ t in (14 : ℝ)..T, ∑ ρ ∈ s, Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t) =
          ∑ ρ ∈ s, ∫ t in (14 : ℝ)..T, Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t := by
    intro s
    induction s using Finset.cons_induction with
    | empty => intro _; simp
    | cons a s ha ih =>
      intro hs
      simp only [Finset.sum_cons]
      have h1 := hs a (Finset.mem_cons_self a s)
      have hrest : ∀ ρ ∈ s, IntervalIntegrable
          (fun t => Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t)
          MeasureTheory.volume 14 T := fun ρ hρ => hs ρ (Finset.mem_cons_of_mem hρ)
      have hsum_int : IntervalIntegrable
          (fun t => ∑ ρ ∈ s, Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t)
          MeasureTheory.volume 14 T := by
        clear ih hs ha
        revert hrest
        induction s using Finset.cons_induction with
        | empty => intro _; simp
        | cons b s' _ ih' =>
          intro hrest
          simp only [Finset.sum_cons]
          exact (hrest b (Finset.mem_cons_self b s')).add
            (ih' (fun ρ hρ => hrest ρ (Finset.mem_cons_of_mem hρ)))
      rw [intervalIntegral.integral_add h1 hsum_int, ih hrest]
  rw [hint_eq, hint_sum A (fun ρ hρ => (hint_piece ρ hρ).1)]
  have hsum_eval :
      (∑ ρ ∈ A, ∫ t in (14 : ℝ)..T, Set.indicator (Set.Ici ρ.im) (fun _ => (1 : ℝ)) t * f' t) =
        ∑ ρ ∈ A, (f T - f ρ.im) :=
    Finset.sum_congr rfl (fun ρ hρ => (hint_piece ρ hρ).2)
  rw [hsum_eval, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hA_card]
  ring

/-- Descomposición exacta de la suma sobre ceros hasta altura `T` en término principal `M(t)`
    y término de error `R(t) = N(t) - M(t)` mediante integración por partes. -/
lemma abel_summation_zeros_decomp {T : ℝ} (hT : 14 ≤ T) (h0 : zeroCount 14 = 0)
    {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (14 : ℝ) T, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc (14 : ℝ) T)) :
    ∑ ρ ∈ (nontrivialZerosUpTo_finite T).toFinset, f ρ.im =
      rvmMainTerm 14 * f 14
      + ((zeroCount T : ℝ) - rvmMainTerm T) * f T
      + (∫ t in (14 : ℝ)..T, (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * f t)
      - (∫ t in (14 : ℝ)..T, ((zeroCount t : ℝ) - rvmMainTerm t) * f' t) := by
  have habel := abel_summation_zeros hT h0 hf hf'
  have hM_deriv : ∀ t ∈ Set.uIcc (14 : ℝ) T,
      HasDerivAt rvmMainTerm ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact rvmMainTerm_hasDerivAt (by linarith [ht.1])
  have hf_deriv : ∀ t ∈ Set.uIcc (14 : ℝ) T, HasDerivAt f (f' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact hf t ht
  have hM'_cont : ContinuousOn (fun t : ℝ => (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)))
      (Set.Icc 14 T) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.log (continuousOn_id.div_const _) ?_
    intro t ht
    exact div_ne_zero (by linarith [ht.1]) (by positivity)
  have hM'_int : IntervalIntegrable
      (fun t : ℝ => (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)))
      MeasureTheory.volume 14 T :=
    hM'_cont.intervalIntegrable_of_Icc hT
  have hf'_int : IntervalIntegrable f' MeasureTheory.volume 14 T :=
    hf'.intervalIntegrable_of_Icc hT
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hM_deriv hf_deriv hM'_int hf'_int
  -- Integrabilidad de N(t) * f'(t) y M(t) * f'(t) para separar la integral
  have hM_cont : ContinuousOn rvmMainTerm (Set.Icc 14 T) := by
    intro t ht
    exact (rvmMainTerm_hasDerivAt (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hMf'_int : IntervalIntegrable (fun t => rvmMainTerm t * f' t) MeasureTheory.volume 14 T :=
    (hM_cont.mul hf').intervalIntegrable_of_Icc hT
  have hNf'_int : IntervalIntegrable (fun t => (zeroCount t : ℝ) * f' t) MeasureTheory.volume 14 T := by
    set A := (nontrivialZerosUpTo_finite T).toFinset
    have hN_mono : Monotone (fun t : ℝ => (zeroCount t : ℝ)) :=
      fun _ _ h => Nat.cast_le.mpr (zeroCount_mono h)
    have hN_int : IntervalIntegrable (fun t => (zeroCount t : ℝ)) MeasureTheory.volume 14 T :=
      hN_mono.intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hbdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (14 : ℝ) T, ‖f' t‖ ≤ C := by
      rcases (isCompact_Icc (a := (14 : ℝ)) (b := T)).exists_bound_of_continuousOn hf' with ⟨C, hC⟩
      exact ⟨C, hC⟩
    rcases hbdd with ⟨C, hC⟩
    refine MeasureTheory.Integrable.mono' (hN_int.1.norm.const_mul (max C 0)) ?_ ?_
    · exact (hN_int.1.aestronglyMeasurable).mul (hf'_int.1.aestronglyMeasurable)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (le_trans (hC t ⟨ht.1.le, ht.2⟩) (le_max_left _ _)) (norm_nonneg _)
  have hsub_int :
      (∫ t in (14 : ℝ)..T, ((zeroCount t : ℝ) - rvmMainTerm t) * f' t) =
        (∫ t in (14 : ℝ)..T, (zeroCount t : ℝ) * f' t) -
        (∫ t in (14 : ℝ)..T, rvmMainTerm t * f' t) := by
    have hrew : (fun t => ((zeroCount t : ℝ) - rvmMainTerm t) * f' t) =
        (fun t => (zeroCount t : ℝ) * f' t - rvmMainTerm t * f' t) := by ext t; ring
    rw [hrew, intervalIntegral.integral_sub hNf'_int hMf'_int]
  linarith

/-- Derivada de `sincSq(u) = (sin u / u)²` para `u ≠ 0`. -/
noncomputable def sincSqDeriv (u : ℝ) : ℝ :=
  2 * (Real.sin u / u) * ((u * Real.cos u - Real.sin u) / u ^ 2)

lemma sincSq_hasDerivAt {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt sincSq (sincSqDeriv u) u := by
  have hdiv : HasDerivAt (fun x : ℝ => Real.sin x / x)
      ((Real.cos u * u - Real.sin u * 1) / u ^ 2) u :=
    (Real.hasDerivAt_sin u).div (hasDerivAt_id u) hu
  have hsq : HasDerivAt sincSq
      (2 * (Real.sin u / u) ^ (2 - 1) * ((Real.cos u * u - Real.sin u * 1) / u ^ 2)) u :=
    hdiv.pow 2
  have heq : 2 * (Real.sin u / u) ^ (2 - 1) * ((Real.cos u * u - Real.sin u * 1) / u ^ 2) =
      sincSqDeriv u := by
    unfold sincSqDeriv; ring
  rwa [heq] at hsq

lemma sincSq_scaled_hasDerivAt {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => sincSq (x * h / 2)) ((h / 2) * sincSqDeriv (t * h / 2)) t := by
  have hu : t * h / 2 ≠ 0 := by positivity
  have hlin : HasDerivAt (fun x : ℝ => x * h / 2) (h / 2) t := by
    have h1 : HasDerivAt (fun x : ℝ => x * h / 2) (1 * h / 2) t :=
      ((hasDerivAt_id t).mul_const h).div_const 2
    rwa [one_mul] at h1
  simpa [Function.comp_def, mul_comm] using (sincSq_hasDerivAt hu).comp t hlin

lemma sincSq_scaled_deriv_continuousOn {h T : ℝ} (hh : 0 < h) :
    ContinuousOn (fun t : ℝ => (h / 2) * sincSqDeriv (t * h / 2)) (Set.Icc 14 T) := by
  unfold sincSqDeriv
  have hlin : ContinuousOn (fun t : ℝ => t * h / 2) (Set.Icc 14 T) :=
    (continuousOn_id.mul continuousOn_const).div_const 2
  have hne : ∀ t ∈ Set.Icc (14 : ℝ) T, t * h / 2 ≠ 0 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    positivity
  refine continuousOn_const.mul ((continuousOn_const.mul ?_).mul ?_)
  · exact (Real.continuous_sin.continuousOn.comp hlin (Set.mapsTo_univ _ _)).div hlin hne
  · refine ((hlin.mul (Real.continuous_cos.continuousOn.comp hlin (Set.mapsTo_univ _ _))).sub
      (Real.continuous_sin.continuousOn.comp hlin (Set.mapsTo_univ _ _))).div (hlin.pow 2) ?_
    intro t ht
    exact pow_ne_zero 2 (hne t ht)

/-- Cota elemental `sin u ≥ u - u³ / 6` para `0 ≤ u`. -/
lemma sin_ge_sub_cube_div_six {u : ℝ} (hu : 0 ≤ u) : u - u ^ 3 / 6 ≤ Real.sin u := by
  -- Primero 1 - x² / 2 ≤ cos x para x ≥ 0 (derivada x - sin x ≥ 0)
  have hcos : ∀ x : ℝ, 0 ≤ x → 1 - x ^ 2 / 2 ≤ Real.cos x := by
    intro x hx
    have hd : ∀ t ∈ Set.Icc (0 : ℝ) x,
        HasDerivAt (fun y : ℝ => Real.cos y - (1 - y ^ 2 / 2)) (t - Real.sin t) t := by
      intro t _
      have h1 : HasDerivAt (fun y : ℝ => Real.cos y - (1 - y ^ 2 / 2))
          (-Real.sin t - (0 - 2 * t ^ (2 - 1) / 2)) t :=
        (Real.hasDerivAt_cos t).sub ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2))
      have heq : -Real.sin t - (0 - 2 * t ^ (2 - 1) / 2) = t - Real.sin t := by ring
      rwa [heq] at h1
    have hmono : MonotoneOn (fun y : ℝ => Real.cos y - (1 - y ^ 2 / 2)) (Set.Icc 0 x) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      · exact (Real.continuous_cos.sub (continuous_const.sub ((continuous_id.pow 2).div_const 2))).continuousOn
      · intro t ht
        rw [interior_Icc] at ht
        exact (hd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]
        have := Real.sin_le ht.1.le
        linarith
    have h0 := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
    simp only [Real.cos_zero] at h0
    linarith
  -- Ahora sin u - (u - u³ / 6) tiene derivada cos t - (1 - t² / 2) ≥ 0
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) u,
      HasDerivAt (fun y : ℝ => Real.sin y - (y - y ^ 3 / 6)) (Real.cos t - (1 - t ^ 2 / 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun y : ℝ => Real.sin y - (y - y ^ 3 / 6))
        (Real.cos t - (1 - 3 * t ^ (3 - 1) / 6)) t :=
      (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6))
    have heq : Real.cos t - (1 - 3 * t ^ (3 - 1) / 6) = Real.cos t - (1 - t ^ 2 / 2) := by ring
    rwa [heq] at h1
  have hmono : MonotoneOn (fun y : ℝ => Real.sin y - (y - y ^ 3 / 6)) (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · exact (Real.continuous_sin.sub (continuous_id.sub ((continuous_id.pow 3).div_const 6))).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]
      linarith [hcos t ht.1.le]
  have h0 := hmono ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu
  simp only [Real.sin_zero] at h0
  linarith

/-- Cota inferior `1 - u² / 3 ≤ sincSq u` para `0 < u ≤ 1`. -/
lemma one_sub_sq_div_three_le_sincSq {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    1 - u ^ 2 / 3 ≤ sincSq u := by
  have hsin := sin_ge_sub_cube_div_six hu0.le
  have hdiv : 1 - u ^ 2 / 6 ≤ Real.sin u / u := by
    rw [le_div_iff₀ hu0]
    nlinarith
  have hnn : 0 ≤ 1 - u ^ 2 / 6 := by nlinarith
  unfold sincSq
  nlinarith

set_option maxHeartbeats 800000 in
/-- Cota universal `∫_δ^M sincSq u du ≤ π / 2` para cualesquiera `0 < δ ≤ M`,
    demostrada vía Fubini en rectángulo finito `[δ, M] × [a, R]` + FTC. -/
lemma integral_sincSq_le_pi_div_two {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M) :
    (∫ u in δ..M, sincSq u) ≤ Real.pi / 2 := by
  have hM0 : 0 < M := lt_of_lt_of_le hδ hδM
  -- Paso 1: para todo a > 0, ∫_δ^M exp(-2au) * sincSq u du ≤ π / 2
  have hexp_bound : ∀ a : ℝ, 0 < a →
      (∫ u in δ..M, Real.exp (-2 * a * u) * sincSq u) ≤ Real.pi / 2 := by
    intro a ha
    apply le_of_forall_pos_le_add
    intro η hη
    set R : ℝ := max (a + 1) (max 1 ((1 / δ ^ 4 + 1 / δ ^ 3) * (M - δ + 1) / η))
    have haR : a ≤ R := le_trans (by linarith) (le_max_left _ _)
    have hR1 : 1 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
    have hR_big : (1 / δ ^ 4 + 1 / δ ^ 3) * (M - δ + 1) / η ≤ R :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hR0 : 0 < R := by linarith
    -- Identidad exacta en s para u > 0:
    -- 4 * ∫_a^R (s - a) exp(-2su) ds = exp(-2au)/u² - (2(R-a)/u + 1/u²) exp(-2Ru)
    have hs_ftc : ∀ u : ℝ, 0 < u →
        4 * (∫ s in a..R, (s - a) * Real.exp (-2 * s * u)) =
          Real.exp (-2 * a * u) / u ^ 2 - (2 * (R - a) / u + 1 / u ^ 2) * Real.exp (-2 * R * u) := by
      intro u hu
      let Fu : ℝ → ℝ := fun s => (-((s - a) / (2 * u)) - 1 / (4 * u ^ 2)) * Real.exp (-2 * s * u)
      have hFu_deriv : ∀ s ∈ Set.uIcc a R, HasDerivAt Fu ((s - a) * Real.exp (-2 * s * u)) s := by
        intro s _
        have hlin : HasDerivAt (fun x : ℝ => -((x - a) / (2 * u)) - 1 / (4 * u ^ 2)) (-1 / (2 * u)) s := by
          have h1 : HasDerivAt (fun x : ℝ => -((x - a) / (2 * u)) - 1 / (4 * u ^ 2))
              (-((1 - 0) / (2 * u)) - 0) s :=
            (((hasDerivAt_id s).sub (hasDerivAt_const s a)).div_const (2 * u)).neg.sub (hasDerivAt_const s _)
          have heq : -((1 - 0) / (2 * u)) - 0 = -1 / (2 * u) := by ring
          rwa [heq] at h1
        have hexp : HasDerivAt (fun x : ℝ => Real.exp (-2 * x * u)) (Real.exp (-2 * s * u) * (-2 * u)) s := by
          have harg : HasDerivAt (fun x : ℝ => -2 * x * u) (-2 * u) s := by
            have h1 : HasDerivAt (fun x : ℝ => -2 * x * u) ((-2 * 1) * u) s :=
              ((hasDerivAt_id s).const_mul (-2)).mul_const u
            have heq : (-2 * 1) * u = -2 * u := by ring
            rwa [heq] at h1
          exact harg.exp
        have hprod := hlin.mul hexp
        have heq : -1 / (2 * u) * Real.exp (-2 * s * u) +
            (-((s - a) / (2 * u)) - 1 / (4 * u ^ 2)) * (Real.exp (-2 * s * u) * (-2 * u)) =
            (s - a) * Real.exp (-2 * s * u) := by
          have hu' : u ≠ 0 := hu.ne'
          field_simp; ring
        rwa [heq] at hprod
      have hcont : Continuous (fun s : ℝ => (s - a) * Real.exp (-2 * s * u)) :=
        (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp ((continuous_const.mul continuous_id).mul continuous_const))
      have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hFu_deriv (hcont.intervalIntegrable a R)
      rw [hint]
      dsimp [Fu]
      have hu' : u ≠ 0 := hu.ne'
      field_simp; ring
    -- Cota del resto en R para u ∈ [δ, M]
    have htail_u : ∀ u ∈ Set.Icc δ M,
        (2 * (R - a) / u + 1 / u ^ 2) * Real.exp (-2 * R * u) ≤ η / (M - δ + 1) := by
      intro u hu
      have hu_pos : 0 < u := lt_of_lt_of_le hδ hu.1
      have h1 : 2 * (R - a) / u ≤ 2 * R / δ := by
        calc 2 * (R - a) / u ≤ 2 * R / u := div_le_div_of_nonneg_right (by linarith) hu_pos.le
          _ ≤ 2 * R / δ := div_le_div_of_nonneg_left (by positivity) hδ hu.1
      have h2 : 1 / u ^ 2 ≤ 1 / δ ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith [hu.1])
      have hexp_le : Real.exp (-2 * R * u) ≤ Real.exp (-2 * R * δ) :=
        Real.exp_le_exp.mpr (by nlinarith [hu.1])
      have hexp_lb : 2 * R ^ 2 * δ ^ 2 ≤ Real.exp (2 * R * δ) := by
        have htay := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * R * δ by positivity) 3
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at htay
        nlinarith [show 0 ≤ 2 * R * δ by positivity]
      have hexp_inv : Real.exp (-2 * R * δ) ≤ 1 / (2 * R ^ 2 * δ ^ 2) := by
        rw [show -2 * R * δ = -(2 * R * δ) by ring, Real.exp_neg, ← one_div]
        exact one_div_le_one_div_of_le (by positivity) hexp_lb
      have hcomb : (2 * (R - a) / u + 1 / u ^ 2) * Real.exp (-2 * R * u) ≤
          (2 * R / δ + 1 / δ ^ 2) * (1 / (2 * R ^ 2 * δ ^ 2)) :=
        mul_le_mul (by linarith) (le_trans hexp_le hexp_inv) (Real.exp_pos _).le (by positivity)
      have hsimp : (2 * R / δ + 1 / δ ^ 2) * (1 / (2 * R ^ 2 * δ ^ 2)) ≤ (1 / δ ^ 4 + 1 / δ ^ 3) / R := by
        have hrew1 : (2 * R / δ + 1 / δ ^ 2) * (1 / (2 * R ^ 2 * δ ^ 2)) =
            (1 / δ ^ 3) / R + (1 / (2 * δ ^ 4)) / R ^ 2 := by
          have hδ' : δ ≠ 0 := hδ.ne'
          have hR' : R ≠ 0 := hR0.ne'
          field_simp
        have hrew2 : (1 / (2 * δ ^ 4)) / R ^ 2 ≤ (1 / δ ^ 4) / R := by
          have hRsq : R ≤ R ^ 2 := by nlinarith
          have hδ4 : 0 < δ ^ 4 := by positivity
          have h1 : (1 / (2 * δ ^ 4)) / R ^ 2 ≤ (1 / δ ^ 4) / R ^ 2 :=
            div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) hδ4 (by linarith)) (by positivity)
          have h2 : (1 / δ ^ 4) / R ^ 2 ≤ (1 / δ ^ 4) / R :=
            div_le_div_of_nonneg_left (by positivity) hR0 hRsq
          exact le_trans h1 h2
        rw [hrew1, add_div]
        linarith
      have hfinal : (1 / δ ^ 4 + 1 / δ ^ 3) / R ≤ η / (M - δ + 1) := by
        rw [div_le_div_iff₀ hR0 (by linarith)]
        rw [div_le_iff₀ hη] at hR_big
        linarith
      exact le_trans hcomb (le_trans hsimp hfinal)
    -- Cota puntual en u ∈ [δ, M]
    have hpt : ∀ u ∈ Set.Icc δ M,
        Real.exp (-2 * a * u) * sincSq u ≤
          4 * (∫ s in a..R, (s - a) * Real.exp (-2 * s * u) * Real.sin u ^ 2) + η / (M - δ + 1) := by
      intro u hu
      have hu_pos : 0 < u := lt_of_lt_of_le hδ hu.1
      have hsin_sq_le : Real.sin u ^ 2 ≤ 1 := by
        have := Real.sin_sq_add_cos_sq u
        nlinarith [sq_nonneg (Real.cos u)]
      have hsin_sq_nn : 0 ≤ Real.sin u ^ 2 := sq_nonneg _
      have h1 := hs_ftc u hu_pos
      have hmul_int : (∫ s in a..R, (s - a) * Real.exp (-2 * s * u) * Real.sin u ^ 2) =
          (∫ s in a..R, (s - a) * Real.exp (-2 * s * u)) * Real.sin u ^ 2 :=
        intervalIntegral.integral_mul_const _ _
      rw [hmul_int]
      have h2 : Real.exp (-2 * a * u) * sincSq u =
          4 * ((∫ s in a..R, (s - a) * Real.exp (-2 * s * u)) * Real.sin u ^ 2) +
          (2 * (R - a) / u + 1 / u ^ 2) * Real.exp (-2 * R * u) * Real.sin u ^ 2 := by
        unfold sincSq
        rw [div_pow]
        have h3 : Real.exp (-2 * a * u) * (Real.sin u ^ 2 / u ^ 2) =
            (Real.exp (-2 * a * u) / u ^ 2) * Real.sin u ^ 2 := by ring
        rw [h3]
        have h4 : Real.exp (-2 * a * u) / u ^ 2 =
            4 * (∫ s in a..R, (s - a) * Real.exp (-2 * s * u)) +
            (2 * (R - a) / u + 1 / u ^ 2) * Real.exp (-2 * R * u) := by linarith
        rw [h4]; ring
      rw [h2]
      have h3 : (2 * (R - a) / u + 1 / u ^ 2) * Real.exp (-2 * R * u) * Real.sin u ^ 2 ≤
          (2 * (R - a) / u + 1 / u ^ 2) * Real.exp (-2 * R * u) :=
        mul_le_of_le_one_right (by positivity) hsin_sq_le
      linarith [htail_u u hu]
    -- Integrabilidad y Fubini en [δ, M] × [a, R]
    let K : ℝ × ℝ → ℝ := fun p => (p.2 - a) * Real.exp (-2 * p.2 * p.1) * Real.sin p.1 ^ 2
    have hK_cont : Continuous K := by
      dsimp [K]
      fun_prop
    have hK_int : MeasureTheory.IntegrableOn K (Set.uIoc δ M ×ˢ Set.uIoc a R) MeasureTheory.volume := by
      have hcomp : IsCompact (Set.Icc δ M ×ˢ Set.Icc a R) := isCompact_Icc.prod isCompact_Icc
      have hint_icc := hK_cont.continuousOn.integrableOn_compact (μ := MeasureTheory.volume) hcomp
      refine hint_icc.mono_set ?_
      rw [Set.uIoc_of_le hδM, Set.uIoc_of_le haR]
      exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
    have hfub :
        (∫ u in δ..M, ∫ s in a..R, K (u, s)) = ∫ s in a..R, ∫ u in δ..M, K (u, s) :=
      MeasureTheory.intervalIntegral_intervalIntegral_swap hK_int
    -- Cota de la integral interior en u para cada s > 0: ∫_δ^M exp(-2su) sin² u du ≤ 1 / (4s(s²+1))
    have hu_bound : ∀ s : ℝ, 0 < s →
        (∫ u in δ..M, Real.exp (-2 * s * u) * Real.sin u ^ 2) ≤ 1 / (4 * s * (s ^ 2 + 1)) := by
      intro s hs
      let Gs : ℝ → ℝ := fun u =>
        Real.exp (-2 * s * u) * (-1 / (4 * s) + (s * Real.cos (2 * u) - Real.sin (2 * u)) / (4 * (s ^ 2 + 1)))
      have hGs_deriv : ∀ u ∈ Set.uIcc (0 : ℝ) M, HasDerivAt Gs (Real.exp (-2 * s * u) * Real.sin u ^ 2) u := by
        intro u _
        have hexp : HasDerivAt (fun x : ℝ => Real.exp (-2 * s * x)) (Real.exp (-2 * s * u) * (-2 * s)) u := by
          have harg : HasDerivAt (fun x : ℝ => -2 * s * x) (-2 * s) u := by
            simpa using (hasDerivAt_id u).const_mul (-2 * s)
          exact harg.exp
        have hcos2 : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-Real.sin (2 * u) * 2) u := by
          have harg : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by
            simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
          exact (Real.hasDerivAt_cos (2 * u)).comp u harg
        have hsin2 : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * u) * 2) u := by
          have harg : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by
            simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
          exact (Real.hasDerivAt_sin (2 * u)).comp u harg
        have hnum : HasDerivAt (fun x : ℝ => s * Real.cos (2 * x) - Real.sin (2 * x))
            (s * (-Real.sin (2 * u) * 2) - Real.cos (2 * u) * 2) u :=
          (hcos2.const_mul s).sub hsin2
        have hbr : HasDerivAt
            (fun x : ℝ => -1 / (4 * s) + (s * Real.cos (2 * x) - Real.sin (2 * x)) / (4 * (s ^ 2 + 1)))
            (0 + (s * (-Real.sin (2 * u) * 2) - Real.cos (2 * u) * 2) / (4 * (s ^ 2 + 1))) u :=
          (hasDerivAt_const u _).add (hnum.div_const _)
        have hprod := hexp.mul hbr
        have htrig : Real.cos (2 * u) = 1 - 2 * Real.sin u ^ 2 := by
          have h1 := Real.cos_two_mul' u
          have h2 := Real.sin_sq_add_cos_sq u
          linarith
        have heq : Real.exp (-2 * s * u) * (-2 * s) *
              (-1 / (4 * s) + (s * Real.cos (2 * u) - Real.sin (2 * u)) / (4 * (s ^ 2 + 1))) +
            Real.exp (-2 * s * u) *
              (0 + (s * (-Real.sin (2 * u) * 2) - Real.cos (2 * u) * 2) / (4 * (s ^ 2 + 1))) =
            Real.exp (-2 * s * u) * Real.sin u ^ 2 := by
          have hs' : s ≠ 0 := hs.ne'
          have hs2' : s ^ 2 + 1 ≠ 0 := by positivity
          rw [htrig]
          field_simp; ring
        rwa [heq] at hprod
      have hcont_u : Continuous (fun u : ℝ => Real.exp (-2 * s * u) * Real.sin u ^ 2) := by fun_prop
      have hftc0M := intervalIntegral.integral_eq_sub_of_hasDerivAt hGs_deriv (hcont_u.intervalIntegrable 0 M)
      have hle_0M : (∫ u in δ..M, Real.exp (-2 * s * u) * Real.sin u ^ 2) ≤
          ∫ u in (0 : ℝ)..M, Real.exp (-2 * s * u) * Real.sin u ^ 2 := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hcont_u.intervalIntegrable 0 δ) (hcont_u.intervalIntegrable δ M)]
        have hnn : 0 ≤ ∫ u in (0 : ℝ)..δ, Real.exp (-2 * s * u) * Real.sin u ^ 2 :=
          intervalIntegral.integral_nonneg hδ.le (fun u _ => by positivity)
        linarith
      have hGs0 : Gs 0 = -1 / (4 * s * (s ^ 2 + 1)) := by
        dsimp [Gs]
        simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, mul_one, sub_zero, one_mul]
        have hs' : s ≠ 0 := hs.ne'
        have hs2' : s ^ 2 + 1 ≠ 0 := by positivity
        field_simp; ring
      have hGsM_le : Gs M ≤ 0 := by
        dsimp [Gs]
        have hcs : (s * Real.cos (2 * M) - Real.sin (2 * M)) ^ 2 ≤ s ^ 2 + 1 := by
          have h1 := Real.sin_sq_add_cos_sq (2 * M)
          have h2 := sq_nonneg (s * Real.sin (2 * M) + Real.cos (2 * M))
          nlinarith
        have hnum_le : s * Real.cos (2 * M) - Real.sin (2 * M) ≤ (s ^ 2 + 1) / s := by
          have hsq : ((s ^ 2 + 1) / s) ^ 2 ≥ s ^ 2 + 1 := by
            have hs' : s ≠ 0 := hs.ne'
            have hdiff : ((s ^ 2 + 1) / s) ^ 2 - (s ^ 2 + 1) = (s ^ 2 + 1) / s ^ 2 := by
              field_simp; ring
            have hpos : 0 ≤ (s ^ 2 + 1) / s ^ 2 := by positivity
            linarith
          nlinarith [show 0 < (s ^ 2 + 1) / s by positivity]
        have hbr_le : -1 / (4 * s) + (s * Real.cos (2 * M) - Real.sin (2 * M)) / (4 * (s ^ 2 + 1)) ≤ 0 := by
          have h1 : (s * Real.cos (2 * M) - Real.sin (2 * M)) / (4 * (s ^ 2 + 1)) ≤
              ((s ^ 2 + 1) / s) / (4 * (s ^ 2 + 1)) :=
            div_le_div_of_nonneg_right hnum_le (by positivity)
          have h2 : ((s ^ 2 + 1) / s) / (4 * (s ^ 2 + 1)) = 1 / (4 * s) := by
            have hs' : s ≠ 0 := hs.ne'
            have hs2' : s ^ 2 + 1 ≠ 0 := by positivity
            field_simp
          have h3 : -1 / (4 * s) = -(1 / (4 * s)) := by ring
          linarith
        exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hbr_le
      have hGs0' : -Gs 0 = 1 / (4 * s * (s ^ 2 + 1)) := by rw [hGs0]; ring
      linarith
    -- Integración final en s de a a R usando arctan
    have houter : 4 * (∫ s in a..R, ∫ u in δ..M, K (u, s)) ≤ Real.pi / 2 := by
      have hstep : ∀ s ∈ Set.Icc a R,
          4 * (∫ u in δ..M, K (u, s)) ≤ 1 / (s ^ 2 + 1) := by
        intro s hs
        have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
        have hrew : (fun u => K (u, s)) = (fun u => (s - a) * (Real.exp (-2 * s * u) * Real.sin u ^ 2)) := by
          ext u; dsimp [K]; ring
        rw [hrew, intervalIntegral.integral_const_mul]
        have h1 : 4 * ((s - a) * ∫ u in δ..M, Real.exp (-2 * s * u) * Real.sin u ^ 2) ≤
            4 * ((s - a) * (1 / (4 * s * (s ^ 2 + 1)))) := by
          have hsm : 0 ≤ s - a := by linarith [hs.1]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hu_bound s hs0) hsm) (by norm_num)
        have h2 : 4 * ((s - a) * (1 / (4 * s * (s ^ 2 + 1)))) ≤ 1 / (s ^ 2 + 1) := by
          have hs' : s ≠ 0 := hs0.ne'
          have hs2' : s ^ 2 + 1 ≠ 0 := by positivity
          have hrew2 : 4 * ((s - a) * (1 / (4 * s * (s ^ 2 + 1)))) = ((s - a) / s) * (1 / (s ^ 2 + 1)) := by
            field_simp
          rw [hrew2]
          have hfrac : (s - a) / s ≤ 1 := by rw [div_le_one hs0]; linarith
          exact mul_le_of_le_one_left (by positivity) hfrac
        exact le_trans h1 h2
      have hcont_inner : ContinuousOn (fun s => 4 * ∫ u in δ..M, K (u, s)) (Set.Icc a R) := by
        have h1 : Continuous (fun s => ∫ u in δ..M, K (u, s)) :=
          intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
            (f := fun s u => K (u, s)) (hK_cont.comp continuous_swap) δ M
        exact (continuous_const.mul h1).continuousOn
      have hcont_arc : Continuous (fun s : ℝ => 1 / (s ^ 2 + 1)) :=
        continuous_const.div ((continuous_id.pow 2).add continuous_const)
          (fun s => (by nlinarith [sq_nonneg s] : s ^ 2 + 1 ≠ 0))
      have hmono : (∫ s in a..R, 4 * ∫ u in δ..M, K (u, s)) ≤ ∫ s in a..R, 1 / (s ^ 2 + 1) :=
        intervalIntegral.integral_mono_on haR
          (hcont_inner.intervalIntegrable_of_Icc haR)
          (hcont_arc.intervalIntegrable a R) hstep
      rw [intervalIntegral.integral_const_mul] at hmono
      have harctan : (∫ s in a..R, 1 / (s ^ 2 + 1)) = Real.arctan R - Real.arctan a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro s _
          have h1 := Real.hasDerivAt_arctan s
          rwa [add_comm (1 : ℝ) (s ^ 2)] at h1
        · exact hcont_arc.intervalIntegrable a R
      have hR_lt : Real.arctan R < Real.pi / 2 := Real.arctan_lt_pi_div_two R
      have ha_pos : 0 < Real.arctan a := Real.arctan_pos.mpr ha
      linarith
    -- Integramos la cota puntual hpt en u ∈ [δ, M]
    have hcont_lhs : ContinuousOn (fun u => Real.exp (-2 * a * u) * sincSq u) (Set.Icc δ M) := by
      refine (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul ?_
      unfold sincSq
      exact (Real.continuous_sin.continuousOn.div continuousOn_id
        (fun u (hu : u ∈ Set.Icc δ M) => (lt_of_lt_of_le hδ hu.1).ne')).pow 2
    have hcont_rhs : Continuous (fun u => 4 * (∫ s in a..R, K (u, s)) + η / (M - δ + 1)) := by
      have h1 : Continuous (fun u => ∫ s in a..R, K (u, s)) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun u s => K (u, s)) hK_cont a R
      exact (continuous_const.mul h1).add continuous_const
    have hint_le : (∫ u in δ..M, Real.exp (-2 * a * u) * sincSq u) ≤
        ∫ u in δ..M, (4 * (∫ s in a..R, K (u, s)) + η / (M - δ + 1)) :=
      intervalIntegral.integral_mono_on hδM
        (hcont_lhs.intervalIntegrable_of_Icc hδM)
        (hcont_rhs.intervalIntegrable δ M) hpt
    have hsplit_rhs : (∫ u in δ..M, (4 * (∫ s in a..R, K (u, s)) + η / (M - δ + 1))) =
        4 * (∫ u in δ..M, ∫ s in a..R, K (u, s)) + (M - δ) * (η / (M - δ + 1)) := by
      have h1 : Continuous (fun u => ∫ s in a..R, K (u, s)) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun u s => K (u, s)) hK_cont a R
      have h4 : Continuous (fun u => 4 * ∫ s in a..R, K (u, s)) := continuous_const.mul h1
      rw [intervalIntegral.integral_add (h4.intervalIntegrable δ M) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    have htail_le : (M - δ) * (η / (M - δ + 1)) ≤ η := by
      have h1 : M - δ ≤ M - δ + 1 := by linarith
      have h2 : (M - δ) / (M - δ + 1) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
      have hrew : (M - δ) * (η / (M - δ + 1)) = ((M - δ) / (M - δ + 1)) * η := by ring
      rw [hrew]
      exact mul_le_of_le_one_left hη.le h2
    rw [hfub] at hsplit_rhs
    linarith
  -- Paso 2: dejar a → 0+ usando exp(-2aM) * ∫ sincSq ≤ ∫ exp(-2au) sincSq ≤ π/2
  apply le_of_forall_pos_le_add
  intro ε hε
  set a : ℝ := min (1 / (2 * M)) (ε / (4 * M * Real.pi))
  have ha0 : 0 < a := lt_min (by positivity) (by positivity)
  have h2aM_le1 : 2 * a * M ≤ 1 := by
    have h1 : a ≤ 1 / (2 * M) := min_le_left _ _
    have h2 : 2 * M * a ≤ 1 := by rwa [le_div_iff₀ (by positivity), mul_comm] at h1
    linarith
  have hcont_s : ContinuousOn sincSq (Set.Icc δ M) := by
    unfold sincSq
    exact (Real.continuous_sin.continuousOn.div continuousOn_id
      (fun u (hu : u ∈ Set.Icc δ M) => (lt_of_lt_of_le hδ hu.1).ne')).pow 2
  have hcont_es : ContinuousOn (fun u => Real.exp (-2 * a * u) * sincSq u) (Set.Icc δ M) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hcont_s
  have hmono_a : Real.exp (-2 * a * M) * (∫ u in δ..M, sincSq u) ≤
      ∫ u in δ..M, Real.exp (-2 * a * u) * sincSq u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hδM
      ((continuousOn_const.mul hcont_s).intervalIntegrable_of_Icc hδM)
      (hcont_es.intervalIntegrable_of_Icc hδM)
    intro u hu
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hu.2])) (sincSq_nonneg u)
  have hle_pi : Real.exp (-2 * a * M) * (∫ u in δ..M, sincSq u) ≤ Real.pi / 2 :=
    le_trans hmono_a (hexp_bound a ha0)
  have hmul_exp : (∫ u in δ..M, sincSq u) ≤ Real.exp (2 * a * M) * (Real.pi / 2) := by
    have h1 := mul_le_mul_of_nonneg_left hle_pi (Real.exp_pos (2 * a * M)).le
    rw [← mul_assoc, ← Real.exp_add, show 2 * a * M + -2 * a * M = 0 by ring, Real.exp_zero, one_mul] at h1
    exact h1
  -- Para 0 ≤ y ≤ 1, exp y ≤ 1 + 2y (vía 1 - y ≤ exp(-y) no; vía exp y ≤ 1 / (1 - y/2)? No: Real.exp_bound o e^y ≤ 1 + (e-1)*y)
  have hexp_lin : Real.exp (2 * a * M) ≤ 1 + 2 * (2 * a * M) := by
    have hconv : Real.exp (2 * a * M) ≤ (1 - 2 * a * M) * Real.exp 0 + (2 * a * M) * Real.exp 1 := by
      have h1 := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
        (show 0 ≤ 1 - 2 * a * M by linarith) (show 0 ≤ 2 * a * M by positivity) (by ring)
      simpa [smul_eq_mul] using h1
    rw [Real.exp_zero, mul_one] at hconv
    have he3 : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
    nlinarith [show 0 ≤ 2 * a * M by positivity]
  have h4aM : 4 * a * M * (Real.pi / 2) ≤ ε := by
    have h1 : a ≤ ε / (4 * M * Real.pi) := min_le_right _ _
    have h2 : a * (4 * M * Real.pi) ≤ ε := (le_div_iff₀ (by positivity)).mp h1
    linarith
  nlinarith [Real.pi_pos]

/-- Cota universal `∫_δ^M ln u * sincSq u du ≤ 0` para `0 < δ ≤ 0.0001` y `1 ≤ M`. -/
lemma integral_log_mul_sincSq_le_zero {δ M : ℝ} (hδ : 0 < δ) (hδ_small : δ ≤ 0.0001) (hM1 : 1 ≤ M) :
    (∫ u in δ..M, Real.log u * sincSq u) ≤ 0 := by
  have hδ1 : δ ≤ 1 := by linarith
  have hcont : ∀ {a b : ℝ}, 0 < a → ContinuousOn (fun u => Real.log u * sincSq u) (Set.Icc a b) := by
    intro a b ha
    have hlog : ContinuousOn Real.log (Set.Icc a b) :=
      Real.continuousOn_log.mono (fun u (hu : u ∈ Set.Icc a b) => (lt_of_lt_of_le ha hu.1).ne')
    have hs : ContinuousOn sincSq (Set.Icc a b) := by
      unfold sincSq
      exact (Real.continuous_sin.continuousOn.div continuousOn_id
        (fun u (hu : u ∈ Set.Icc a b) => (lt_of_lt_of_le ha hu.1).ne')).pow 2
    exact hlog.mul hs
  -- Parte 1: en [δ, 1], ∫_δ^1 ln u * sincSq u du ≤ -0.942
  have hpart1 : (∫ u in δ..1, Real.log u * sincSq u) ≤ -0.942 := by
    have hpt : ∀ u ∈ Set.Icc δ 1, Real.log u * sincSq u ≤ Real.log u * (1 - u ^ 2 / 3) := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hδ hu.1
      have hlog_np : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu.2
      have hs_ge := one_sub_sq_div_three_le_sincSq hu0 hu.2
      nlinarith
    have hcont_rhs : ContinuousOn (fun u : ℝ => Real.log u * (1 - u ^ 2 / 3)) (Set.Icc δ 1) :=
      (Real.continuousOn_log.mono (fun u (hu : u ∈ Set.Icc δ 1) => (lt_of_lt_of_le hδ hu.1).ne')).mul
        (continuousOn_const.sub ((continuousOn_id.pow 2).div_const 3))
    have hle : (∫ u in δ..1, Real.log u * sincSq u) ≤ ∫ u in δ..1, Real.log u * (1 - u ^ 2 / 3) :=
      intervalIntegral.integral_mono_on hδ1
        ((hcont hδ).intervalIntegrable_of_Icc hδ1)
        (hcont_rhs.intervalIntegrable_of_Icc hδ1) hpt
    -- FTC exacta para ln u * (1 - u²/3) con primitiva (u ln u - u) - (u³ ln u / 9 - u³ / 27)
    let P : ℝ → ℝ := fun u => (u * Real.log u - u) - (u ^ 3 * Real.log u / 9 - u ^ 3 / 27)
    have hP_deriv : ∀ u ∈ Set.uIcc δ 1, HasDerivAt P (Real.log u * (1 - u ^ 2 / 3)) u := by
      intro u hu
      rw [Set.uIcc_of_le hδ1] at hu
      have hu0 : 0 < u := lt_of_lt_of_le hδ hu.1
      have hu' : u ≠ 0 := hu0.ne'
      have hlog : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu'
      have h1 : HasDerivAt (fun x : ℝ => x * Real.log x - x) (1 * Real.log u + u * u⁻¹ - 1) u :=
        ((hasDerivAt_id u).mul hlog).sub (hasDerivAt_id u)
      have h2 : HasDerivAt (fun x : ℝ => x ^ 3 * Real.log x / 9 - x ^ 3 / 27)
          (((3 * u ^ (3 - 1)) * Real.log u + u ^ 3 * u⁻¹) / 9 - (3 * u ^ (3 - 1)) / 27) u :=
        (((hasDerivAt_pow 3 u).mul hlog).div_const 9).sub ((hasDerivAt_pow 3 u).div_const 27)
      have hsub := h1.sub h2
      have heq : 1 * Real.log u + u * u⁻¹ - 1 -
          ((3 * u ^ (3 - 1) * Real.log u + u ^ 3 * u⁻¹) / 9 - 3 * u ^ (3 - 1) / 27) =
          Real.log u * (1 - u ^ 2 / 3) := by
        field_simp; ring
      rwa [heq] at hsub
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hP_deriv (hcont_rhs.intervalIntegrable_of_Icc hδ1)
    rw [hftc] at hle
    have hP1 : P 1 = -26 / 27 := by dsimp [P]; simp; ring
    have hneg_dlog : -(δ * Real.log δ) ≤ 2 * Real.sqrt δ := by
      have hs0 : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
      have h1 : -Real.log δ = 2 * Real.log (1 / Real.sqrt δ) := by
        rw [Real.log_div (by norm_num) hs0.ne', Real.log_one, zero_sub, Real.log_sqrt hδ.le]; ring
      have h2 : Real.log (1 / Real.sqrt δ) ≤ 1 / Real.sqrt δ - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h3 : -(δ * Real.log δ) = δ * (-Real.log δ) := by ring
      rw [h3, h1]
      have hsq : δ * (1 / Real.sqrt δ) = Real.sqrt δ := by
        rw [mul_one_div, div_eq_iff hs0.ne', Real.mul_self_sqrt hδ.le]
      nlinarith
    have hsqrt_le : Real.sqrt δ ≤ 0.01 := by
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    have hdlog_np : δ ^ 3 * Real.log δ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos hδ.le hδ1)
    have hPδ_ge : -0.0205 ≤ P δ := by
      dsimp [P]
      have hd3_nn : 0 ≤ δ ^ 3 := by positivity
      linarith
    linarith
  -- Parte 2: en [1, M], extendemos a M' = max M π y partimos en [1, 2.2], [2.2, π], [π, M']
  set M' : ℝ := max M Real.pi
  have hM_le_M' : M ≤ M' := le_max_left _ _
  have hpi_le_M' : Real.pi ≤ M' := le_max_right _ _
  have hpart2 : (∫ u in (1 : ℝ)..M, Real.log u * sincSq u) ≤ 0.94 := by
    have hext : (∫ u in (1 : ℝ)..M, Real.log u * sincSq u) ≤ ∫ u in (1 : ℝ)..M', Real.log u * sincSq u := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        ((hcont (by norm_num)).intervalIntegrable_of_Icc hM1)
        ((hcont (by linarith)).intervalIntegrable_of_Icc hM_le_M')]
      have hnn : 0 ≤ ∫ u in M..M', Real.log u * sincSq u :=
        intervalIntegral.integral_nonneg hM_le_M'
          (fun u hu => mul_nonneg (Real.log_nonneg (le_trans hM1 hu.1)) (sincSq_nonneg u))
      linarith
    -- FTC para ln u / u² en cualquier [a, b] con 0 < a ≤ b
    have hlog_div_sq : ∀ {a b : ℝ}, 0 < a → a ≤ b →
        (∫ u in a..b, Real.log u / u ^ 2) = (1 + Real.log a) / a - (1 + Real.log b) / b := by
      intro a b ha hab
      let Q : ℝ → ℝ := fun u => -(1 + Real.log u) / u
      have hQ_deriv : ∀ u ∈ Set.uIcc a b, HasDerivAt Q (Real.log u / u ^ 2) u := by
        intro u hu
        rw [Set.uIcc_of_le hab] at hu
        have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
        have hu' : u ≠ 0 := hu0.ne'
        have hnum : HasDerivAt (fun x : ℝ => -(1 + Real.log x)) (-(0 + u⁻¹)) u :=
          ((hasDerivAt_const u (1 : ℝ)).add (Real.hasDerivAt_log hu')).neg
        have hdiv := hnum.div (hasDerivAt_id u) hu'
        dsimp only [id] at hdiv
        have heq : (-(0 + u⁻¹) * u - -(1 + Real.log u) * 1) / u ^ 2 = Real.log u / u ^ 2 := by
          field_simp; ring
        rwa [heq] at hdiv
      have hcont_q : ContinuousOn (fun u => Real.log u / u ^ 2) (Set.Icc a b) :=
        (Real.continuousOn_log.mono (fun u (hu : u ∈ Set.Icc a b) => (lt_of_lt_of_le ha hu.1).ne')).div
          (continuousOn_id.pow 2) (fun u hu => pow_ne_zero 2 (lt_of_lt_of_le ha hu.1).ne')
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hQ_deriv (hcont_q.intervalIntegrable_of_Icc hab)
      rw [hftc]; dsimp [Q]; ring
    have hle_log_sq : ∀ {a b : ℝ}, 1 ≤ a → a ≤ b →
        (∫ u in a..b, Real.log u * sincSq u) ≤ (1 + Real.log a) / a - (1 + Real.log b) / b := by
      intro a b ha1 hab
      have ha0 : 0 < a := by linarith
      have hcont_q : ContinuousOn (fun u => Real.log u / u ^ 2) (Set.Icc a b) :=
        (Real.continuousOn_log.mono (fun u (hu : u ∈ Set.Icc a b) => (lt_of_lt_of_le ha0 hu.1).ne')).div
          (continuousOn_id.pow 2) (fun u hu => pow_ne_zero 2 (lt_of_lt_of_le ha0 hu.1).ne')
      rw [← hlog_div_sq ha0 hab]
      apply intervalIntegral.integral_mono_on hab
        ((hcont ha0).intervalIntegrable_of_Icc hab)
        (hcont_q.intervalIntegrable_of_Icc hab)
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
      have hlog_nn : 0 ≤ Real.log u := Real.log_nonneg (le_trans ha1 hu.1)
      have hs_le : sincSq u ≤ 1 / u ^ 2 := sincSq_le_inv_sq hu0.ne'
      calc Real.log u * sincSq u ≤ Real.log u * (1 / u ^ 2) := mul_le_mul_of_nonneg_left hs_le hlog_nn
        _ = Real.log u / u ^ 2 := by ring
    -- Cotas logarítmicas elementales: ln(2.2) ≥ 0.785, ln(π) ≤ 1.15
    have hlog22 : (0.785 : ℝ) ≤ Real.log 2.2 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have he_ub : Real.exp 1 ≤ (2.71829 : ℝ) := le_trans Real.exp_one_lt_d9.le (by norm_num)
      -- (exp 0.788)^250 es grande; usamos 0.78 = 39/50? Mejor 0.785? No, 0.78 = 39/50: 2.71829^39 ≤ 2.2^50
      -- Aún más simple: 0.75 = 3/4! Comprobamos: 1 - 1.75/2.2 = 0.2045! Con 0.75: 0.2045 + 0.067 + 0.684 = 0.955 > 0.942!
      -- Con 0.78: 1 - 1.78/2.2 = 0.1909, 0.1909 + 0.0662 + 0.6844 = 0.9415 < 0.942!
      -- Usamos 0.7875? Mejor: 0.78 = 39/50 o 4/5 = 0.8 (ln 2.2 = 0.78845 < 0.8).
      -- Usamos 11/14 ≈ 0.7857: 2.71829^11 = 60292 < 61385 = 2.2^14!!
      have hpow : (Real.exp (11 / 14 : ℝ)) ^ 14 = (Real.exp 1) ^ 11 := by
        rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul]; norm_num
      have hle : (Real.exp (11 / 14 : ℝ)) ^ 14 ≤ (2.2 : ℝ) ^ 14 := by
        rw [hpow]
        calc (Real.exp 1) ^ 11 ≤ (2.71829 : ℝ) ^ 11 := by gcongr
          _ ≤ (2.2 : ℝ) ^ 14 := by norm_num
      have h1114 : Real.exp (11 / 14 : ℝ) ≤ 2.2 := by
        by_contra hcon; push Not at hcon
        have : (2.2 : ℝ) ^ 14 < (Real.exp (11 / 14 : ℝ)) ^ 14 := by gcongr
        linarith
      exact le_trans (Real.exp_le_exp.mpr (by norm_num : (0.785 : ℝ) ≤ 11 / 14)) h1114
    -- Corregimos el objetivo de hlog22 a 0.785
    have hlogpi : Real.log Real.pi ≤ 1.15 := by
      have hpi_ub : Real.pi ≤ 3.1416 := Real.pi_lt_d4.le
      refine le_trans (Real.log_le_log Real.pi_pos hpi_ub) ?_
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he_lb : (2.71828 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      have hpow : (Real.exp 1.15) ^ 20 = (Real.exp 1) ^ 23 := by
        rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul]; norm_num
      have hle : (3.1416 : ℝ) ^ 20 ≤ (Real.exp 1.15) ^ 20 := by
        rw [hpow]
        calc (3.1416 : ℝ) ^ 20 ≤ (2.71828 : ℝ) ^ 23 := by norm_num
          _ ≤ (Real.exp 1) ^ 23 := by gcongr
      by_contra hcon; push Not at hcon
      have : (Real.exp 1.15) ^ 20 < (3.1416 : ℝ) ^ 20 := by gcongr
      linarith
    have h22_le_pi : (2.2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    -- Subintervalo [1, 2.2]
    have hI1 : (∫ u in (1 : ℝ)..2.2, Real.log u * sincSq u) ≤ 0.189 := by
      have h := hle_log_sq le_rfl (by norm_num : (1 : ℝ) ≤ 2.2)
      rw [Real.log_one] at h
      have : (1 + (0.785 : ℝ)) / 2.2 ≤ (1 + Real.log 2.2) / 2.2 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      linarith
    -- Subintervalo [2.2, π]: sin u = sin(π - u) ≤ π - u, ln u ≤ 1.15, u ≥ 2.2
    have hI2 : (∫ u in (2.2 : ℝ)..Real.pi, Real.log u * sincSq u) ≤ 0.0665 := by
      have hpt : ∀ u ∈ Set.Icc (2.2 : ℝ) Real.pi,
          Real.log u * sincSq u ≤ (1.15 / 2.2 ^ 2) * (Real.pi - u) ^ 2 := by
        intro u hu
        have hu0 : 0 < u := by linarith [hu.1]
        have hsin_nn : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu0.le hu.2
        have hsin_le : Real.sin u ≤ Real.pi - u := by
          rw [← Real.sin_pi_sub]
          exact Real.sin_le (by linarith [hu.2])
        have hsinc_le : sincSq u ≤ (Real.pi - u) ^ 2 / 2.2 ^ 2 := by
          unfold sincSq
          rw [div_pow]
          have h1 : Real.sin u ^ 2 ≤ (Real.pi - u) ^ 2 := by nlinarith
          have h2 : (Real.pi - u) ^ 2 / u ^ 2 ≤ (Real.pi - u) ^ 2 / 2.2 ^ 2 :=
            div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by nlinarith [hu.1])
          exact le_trans (div_le_div_of_nonneg_right h1 (by positivity)) h2
        have hlog_le : Real.log u ≤ 1.15 :=
          le_trans (Real.log_le_log hu0 hu.2) hlogpi
        have hlog_nn : 0 ≤ Real.log u := Real.log_nonneg (by linarith [hu.1])
        calc Real.log u * sincSq u ≤ 1.15 * ((Real.pi - u) ^ 2 / 2.2 ^ 2) :=
              mul_le_mul hlog_le hsinc_le (sincSq_nonneg u) (by norm_num)
          _ = (1.15 / 2.2 ^ 2) * (Real.pi - u) ^ 2 := by ring
      have hcont_r : Continuous (fun u : ℝ => (1.15 / 2.2 ^ 2) * (Real.pi - u) ^ 2) := by fun_prop
      have hle : (∫ u in (2.2 : ℝ)..Real.pi, Real.log u * sincSq u) ≤
          ∫ u in (2.2 : ℝ)..Real.pi, (1.15 / 2.2 ^ 2) * (Real.pi - u) ^ 2 :=
        intervalIntegral.integral_mono_on h22_le_pi
          ((hcont (by norm_num)).intervalIntegrable_of_Icc h22_le_pi)
          (hcont_r.intervalIntegrable 2.2 Real.pi) hpt
      have hftc : (∫ u in (2.2 : ℝ)..Real.pi, (1.15 / 2.2 ^ 2) * (Real.pi - u) ^ 2) =
          (1.15 / 2.2 ^ 2) * ((Real.pi - 2.2) ^ 3 / 3) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have hderiv : ∀ u ∈ Set.uIcc (2.2 : ℝ) Real.pi,
            HasDerivAt (fun x : ℝ => -((Real.pi - x) ^ 3 / 3)) ((Real.pi - u) ^ 2) u := by
          intro u _
          have harg : HasDerivAt (fun x : ℝ => Real.pi - x) (-1) u := by
            have h0 : HasDerivAt (fun x : ℝ => Real.pi - x) (0 - 1) u :=
              (hasDerivAt_const u Real.pi).sub (hasDerivAt_id u)
            rwa [zero_sub] at h0
          have h1 : HasDerivAt (fun x : ℝ => -((Real.pi - x) ^ 3 / 3))
              (-(3 * (Real.pi - u) ^ (3 - 1) * (-1) / 3)) u :=
            ((harg.pow 3).div_const 3).neg
          have heq : -(3 * (Real.pi - u) ^ (3 - 1) * (-1) / 3) = (Real.pi - u) ^ 2 := by ring
          rwa [heq] at h1
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
          ((by fun_prop : Continuous fun x : ℝ => (Real.pi - x) ^ 2).intervalIntegrable 2.2 Real.pi)
        rw [h]; ring
      rw [hftc] at hle
      have hpi_ub : Real.pi < 3.1416 := Real.pi_lt_d4
      have hdiff : Real.pi - 2.2 ≤ 0.9416 := by linarith
      have hcube : (Real.pi - 2.2) ^ 3 ≤ 0.9416 ^ 3 := by
        have hnn : 0 ≤ Real.pi - 2.2 := by linarith
        nlinarith [sq_nonneg (Real.pi - 2.2)]
      nlinarith
    -- Subintervalo [π, M']
    have hI3 : (∫ u in Real.pi..M', Real.log u * sincSq u) ≤ 0.6845 := by
      have h := hle_log_sq (by linarith [Real.pi_gt_three]) hpi_le_M'
      have hM'_pos : 0 < M' := lt_of_lt_of_le Real.pi_pos hpi_le_M'
      have hM'_ge1 : 1 ≤ M' := le_trans (by linarith [Real.pi_gt_three]) hpi_le_M'
      have hlogM'_nn : 0 ≤ Real.log M' := Real.log_nonneg hM'_ge1
      have hsub_nn : 0 ≤ (1 + Real.log M') / M' := by positivity
      have hpi_lb : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
      have h1 : (1 + Real.log Real.pi) / Real.pi ≤ (1 + 1.15) / 3.1415 :=
        div_le_div₀ (by norm_num) (by linarith) (by norm_num) hpi_lb.le
      linarith
    have hint1 : IntervalIntegrable (fun u => Real.log u * sincSq u) MeasureTheory.volume 1 2.2 :=
      (hcont (by norm_num)).intervalIntegrable_of_Icc (by norm_num)
    have hint2 : IntervalIntegrable (fun u => Real.log u * sincSq u) MeasureTheory.volume 2.2 Real.pi :=
      (hcont (by norm_num)).intervalIntegrable_of_Icc h22_le_pi
    have hint3 : IntervalIntegrable (fun u => Real.log u * sincSq u) MeasureTheory.volume Real.pi M' :=
      (hcont Real.pi_pos).intervalIntegrable_of_Icc hpi_le_M'
    have hsplit : (∫ u in (1 : ℝ)..M', Real.log u * sincSq u) =
        (∫ u in (1 : ℝ)..2.2, Real.log u * sincSq u) +
        (∫ u in (2.2 : ℝ)..Real.pi, Real.log u * sincSq u) +
        (∫ u in Real.pi..M', Real.log u * sincSq u) := by
      have h12 := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      have h13 := intervalIntegral.integral_add_adjacent_intervals (hint1.trans hint2) hint3
      linarith
    linarith
  have hsplit_full := intervalIntegral.integral_add_adjacent_intervals
    ((hcont hδ).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hδ1)
    ((hcont (by norm_num)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hM1)
  linarith

/-- En `(0, π)`, `sincSq` es decreciente: `sincSqDeriv u ≤ 0`. -/
lemma sincSqDeriv_nonpos_on_Ioo_zero_pi {u : ℝ} (hu0 : 0 < u) (hupi : u < Real.pi) :
    sincSqDeriv u ≤ 0 := by
  have hsin_pos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 hupi
  have hg_nonneg : 0 ≤ Real.sin u - u * Real.cos u := by
    have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) u,
        HasDerivAt (fun t : ℝ => Real.sin t - t * Real.cos t) (x * Real.sin x) x := by
      intro x _
      have h3 : HasDerivAt (fun t : ℝ => Real.sin t - t * Real.cos t)
          (Real.cos x - (1 * Real.cos x + x * -Real.sin x)) x :=
        (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))
      have heq : Real.cos x - (1 * Real.cos x + x * -Real.sin x) = x * Real.sin x := by ring
      rwa [heq] at h3
    have hmono : MonotoneOn (fun t : ℝ => Real.sin t - t * Real.cos t) (Set.Icc 0 u) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
      · exact (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).continuousOn
      · intro x hx
        rw [interior_Icc] at hx
        exact (hderiv x ⟨hx.1.le, hx.2.le⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hderiv x ⟨hx.1.le, hx.2.le⟩).deriv]
        have hxsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (lt_trans hx.2 hupi)
        exact mul_nonneg hx.1.le hxsin.le
    have h0 := hmono ⟨le_rfl, hu0.le⟩ ⟨hu0.le, le_rfl⟩ hu0.le
    simpa using h0
  unfold sincSqDeriv
  have h1 : 0 ≤ 2 * (Real.sin u / u) := by positivity
  have h2 : (u * Real.cos u - Real.sin u) / u ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  exact mul_nonpos_of_nonneg_of_nonpos h1 h2

/-- Cota del término principal integral de `sinc²` en `[14, T]` más el término de frontera `2 M(14) sinc²(7h)`. -/
lemma sincSq_main_integral_bound {h T : ℝ} (hh0 : 0 < h) (hh2 : h < 0.02) (hT : 14 ≤ T) :
    2 * rvmMainTerm 14 * sincSq (14 * h / 2) +
    2 * (∫ t in (14 : ℝ)..T, (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * sincSq (t * h / 2))
      ≤ (1 / h) * Real.log (1 / (Real.pi * h)) + 0.02 := by
  -- Paso 1: cambio de variable u = t * (h / 2) en la integral de 14 a T
  let f : ℝ → ℝ := fun u => Real.log (u / (Real.pi * h)) * sincSq u
  have hsub_var :
      2 * (∫ t in (14 : ℝ)..T, (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * sincSq (t * h / 2)) =
        (2 / (Real.pi * h)) * (∫ u in (7 * h)..(T * h / 2), f u) := by
    have hrew : (fun t : ℝ => (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * sincSq (t * h / 2)) =
        (fun t : ℝ => (1 / (2 * Real.pi)) * f (t * (h / 2))) := by
      ext t
      dsimp [f]
      have harg1 : t * (h / 2) / (Real.pi * h) = t / (2 * Real.pi) := by
        have hh' : h ≠ 0 := hh0.ne'
        have hpi' : Real.pi ≠ 0 := Real.pi_pos.ne'
        field_simp
      have harg2 : t * (h / 2) = t * h / 2 := by ring
      rw [harg1, harg2]; ring
    rw [hrew, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_right (f := f) (c := h / 2) (by positivity)]
    rw [smul_eq_mul, show (14 : ℝ) * (h / 2) = 7 * h by ring, show T * (h / 2) = T * h / 2 by ring]
    have hh' : h ≠ 0 := hh0.ne'
    have hpi' : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
  -- Paso 2: elegir δ = min (h / 100) 0.0001 y conectar 2 M(14) sincSq(7h) con ∫_δ^{7h} f u du
  set δ : ℝ := min (h / 100) 0.0001
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ_small : δ ≤ 0.0001 := min_le_right _ _
  have hδ_lt_pih : δ < Real.pi * h := by
    have h1 : δ ≤ h / 100 := min_le_left _ _
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith
  have hpih_le_7h : Real.pi * h ≤ 7 * h := by
    have hpi : Real.pi < 4 := lt_trans Real.pi_lt_d4 (by norm_num)
    nlinarith
  have h7h_le_Th : 7 * h ≤ T * h / 2 := by nlinarith
  have h7h_lt_1 : 7 * h < 1 := by linarith
  -- Primitiva exacta de ln(u / (π h)): F(u) = u * (ln(u / (π h)) - 1)
  let F : ℝ → ℝ := fun u => u * (Real.log (u / (Real.pi * h)) - 1)
  have hF_deriv : ∀ {u : ℝ}, 0 < u → HasDerivAt F (Real.log (u / (Real.pi * h))) u := by
    intro u hu
    have harg : HasDerivAt (fun x : ℝ => x / (Real.pi * h)) (1 / (Real.pi * h)) u :=
      (hasDerivAt_id u).div_const (Real.pi * h)
    have hlog : HasDerivAt (fun x : ℝ => Real.log (x / (Real.pi * h)) - 1)
        ((1 / (Real.pi * h)) / (u / (Real.pi * h)) - 0) u :=
      (harg.log (by positivity)).sub (hasDerivAt_const u 1)
    have hprod := (hasDerivAt_id u).mul hlog
    dsimp only [id] at hprod
    have heq : 1 * (Real.log (u / (Real.pi * h)) - 1) +
        u * ((1 / (Real.pi * h)) / (u / (Real.pi * h)) - 0) = Real.log (u / (Real.pi * h)) := by
      have hu' : u ≠ 0 := hu.ne'
      have hph' : Real.pi * h ≠ 0 := by positivity
      field_simp; ring
    rwa [heq] at hprod
  have hlog_int : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      (∫ u in a..b, Real.log (u / (Real.pi * h))) = F b - F a := by
    intro a b ha hab
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [Set.uIcc_of_le hab] at hu
      exact hF_deriv (lt_of_lt_of_le ha hu.1)
    · have hcont : ContinuousOn (fun u => Real.log (u / (Real.pi * h))) (Set.Icc a b) :=
        Real.continuousOn_log.comp (continuousOn_id.div_const _)
          (fun u hu => (div_pos (lt_of_lt_of_le ha hu.1) (by positivity)).ne')
      exact hcont.intervalIntegrable_of_Icc hab
  have hFδ_neg : F δ < 0 := by
    dsimp [F]
    have hlog_neg : Real.log (δ / (Real.pi * h)) < 0 :=
      Real.log_neg (by positivity) ((div_lt_one (by positivity)).mpr hδ_lt_pih)
    nlinarith
  have hM14_eq : 2 * rvmMainTerm 14 * sincSq (14 * h / 2) =
      (2 / (Real.pi * h)) * (F (7 * h) * sincSq (7 * h)) := by
    unfold rvmMainTerm
    dsimp [F]
    have h14 : (14 : ℝ) * h / 2 = 7 * h := by ring
    have harg1 : 7 * h / (Real.pi * h) = 7 / Real.pi := by
      have hh' : h ≠ 0 := hh0.ne'
      field_simp
    have harg2 : (14 : ℝ) / (2 * Real.pi * Real.exp 1) = (7 / Real.pi) / Real.exp 1 := by ring
    rw [h14, harg1, harg2, Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    have hh' : h ≠ 0 := hh0.ne'
    have hpi' : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp; ring
  have hM14_le : 2 * rvmMainTerm 14 * sincSq (14 * h / 2) ≤
      (2 / (Real.pi * h)) * (∫ u in δ..(7 * h), Real.log (u / (Real.pi * h)) * sincSq (7 * h)) := by
    rw [hM14_eq, intervalIntegral.integral_mul_const, hlog_int hδ0 (le_trans hδ_lt_pih.le hpih_le_7h)]
    have h1 : F (7 * h) ≤ F (7 * h) - F δ := by linarith
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sincSq_nonneg _)) (by positivity)
  -- Acotar la diferencia ∫_δ^{7h} ln(u/(πh)) * (sincSq(7h) - sincSq u) du
  have hf_cont : ∀ {a b : ℝ}, 0 < a → ContinuousOn f (Set.Icc a b) := by
    intro a b ha
    have h1 : ContinuousOn (fun u => Real.log (u / (Real.pi * h))) (Set.Icc a b) :=
      Real.continuousOn_log.comp (continuousOn_id.div_const _)
        (fun u (hu : u ∈ Set.Icc a b) => (div_pos (lt_of_lt_of_le ha hu.1) (by positivity)).ne')
    have h2 : ContinuousOn sincSq (Set.Icc a b) := by
      unfold sincSq
      exact (Real.continuous_sin.continuousOn.div continuousOn_id
        (fun u (hu : u ∈ Set.Icc a b) => (lt_of_lt_of_le ha hu.1).ne')).pow 2
    exact h1.mul h2
  have hdiff_le :
      (2 / (Real.pi * h)) *
        ((∫ u in δ..(7 * h), Real.log (u / (Real.pi * h)) * sincSq (7 * h)) -
         (∫ u in δ..(7 * h), f u)) ≤ 0.02 := by
    have hcont_c : ContinuousOn (fun u => Real.log (u / (Real.pi * h)) * sincSq (7 * h)) (Set.Icc δ (7 * h)) :=
      (Real.continuousOn_log.comp (continuousOn_id.div_const _)
        (fun u (hu : u ∈ Set.Icc δ (7 * h)) => (div_pos (lt_of_lt_of_le hδ0 hu.1) (by positivity)).ne')).mul continuousOn_const
    have hsub : (∫ u in δ..(7 * h), Real.log (u / (Real.pi * h)) * sincSq (7 * h)) -
        (∫ u in δ..(7 * h), f u) =
        ∫ u in δ..(7 * h), Real.log (u / (Real.pi * h)) * (sincSq (7 * h) - sincSq u) := by
      rw [← intervalIntegral.integral_sub
        (hcont_c.intervalIntegrable_of_Icc (le_trans hδ_lt_pih.le hpih_le_7h))
        ((hf_cont hδ0).intervalIntegrable_of_Icc (le_trans hδ_lt_pih.le hpih_le_7h))]
      apply intervalIntegral.integral_congr
      intro u _; dsimp [f]; ring
    rw [hsub]
    have hcont_diff : ContinuousOn (fun u => Real.log (u / (Real.pi * h)) * (sincSq (7 * h) - sincSq u))
        (Set.Icc δ (7 * h)) := by
      have h1 : ContinuousOn (fun u => Real.log (u / (Real.pi * h))) (Set.Icc δ (7 * h)) :=
        Real.continuousOn_log.comp (continuousOn_id.div_const _)
          (fun u (hu : u ∈ Set.Icc δ (7 * h)) => (div_pos (lt_of_lt_of_le hδ0 hu.1) (by positivity)).ne')
      have h2 : ContinuousOn sincSq (Set.Icc δ (7 * h)) := by
        unfold sincSq
        exact (Real.continuous_sin.continuousOn.div continuousOn_id
          (fun u (hu : u ∈ Set.Icc δ (7 * h)) => (lt_of_lt_of_le hδ0 hu.1).ne')).pow 2
      exact h1.mul (continuousOn_const.sub h2)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((hcont_diff.mono (Set.Icc_subset_Icc_right hpih_le_7h)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hδ_lt_pih.le)
      ((hcont_diff.mono (Set.Icc_subset_Icc_left hδ_lt_pih.le)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hpih_le_7h)
    -- En [πh, 7h]: ln(u/(πh)) ≥ 0 y sincSq(7h) ≤ sincSq u (ya que sincSq decrece en (0, π))
    have hpart_hi : (∫ u in (Real.pi * h)..(7 * h),
        Real.log (u / (Real.pi * h)) * (sincSq (7 * h) - sincSq u)) ≤ 0 := by
      have hanti : AntitoneOn sincSq (Set.Icc (Real.pi * h) (7 * h)) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · unfold sincSq
          exact (Real.continuous_sin.continuousOn.div continuousOn_id
            (fun u (hu : u ∈ Set.Icc (Real.pi * h) (7 * h)) => (lt_of_lt_of_le (by positivity) hu.1).ne')).pow 2
        · intro u hu
          rw [interior_Icc] at hu
          exact (sincSq_hasDerivAt (lt_trans (by positivity) hu.1).ne').differentiableAt.differentiableWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          have hu0 : 0 < u := lt_trans (by positivity) hu.1
          have hupi : u < Real.pi := by linarith [hu.2, Real.pi_gt_three]
          rw [(sincSq_hasDerivAt hu0.ne').deriv]
          exact sincSqDeriv_nonpos_on_Ioo_zero_pi hu0 hupi
      have hle0 : (∫ u in (Real.pi * h)..(7 * h),
          Real.log (u / (Real.pi * h)) * (sincSq (7 * h) - sincSq u)) ≤
          ∫ u in (Real.pi * h)..(7 * h), (0 : ℝ) := by
        apply intervalIntegral.integral_mono_on hpih_le_7h
          ((hcont_diff.mono (Set.Icc_subset_Icc_left hδ_lt_pih.le)).intervalIntegrable_of_Icc hpih_le_7h)
          intervalIntegrable_const
        intro u hu
        have hlog_nn : 0 ≤ Real.log (u / (Real.pi * h)) :=
          Real.log_nonneg ((one_le_div (by positivity)).mpr hu.1)
        have hs_le : sincSq (7 * h) ≤ sincSq u := hanti hu ⟨hpih_le_7h, le_rfl⟩ hu.2
        exact mul_nonpos_of_nonneg_of_nonpos hlog_nn (by linarith)
      simpa using hle0
    -- En [δ, πh]: ln(u/(πh)) ≤ 0 y sincSq u - sincSq(7h) ≤ 1 - sincSq(7h) ≤ (7h)² / 3
    have hpart_lo : (∫ u in δ..(Real.pi * h),
        Real.log (u / (Real.pi * h)) * (sincSq (7 * h) - sincSq u)) ≤
        (Real.pi * h) * ((7 * h) ^ 2 / 3) := by
      have hs7_ge : 1 - (7 * h) ^ 2 / 3 ≤ sincSq (7 * h) :=
        one_sub_sq_div_three_le_sincSq (by positivity) h7h_lt_1.le
      have hcont_ub : ContinuousOn (fun u => (-Real.log (u / (Real.pi * h))) * ((7 * h) ^ 2 / 3))
          (Set.Icc δ (Real.pi * h)) :=
        ((Real.continuousOn_log.comp (continuousOn_id.div_const _)
          (fun u (hu : u ∈ Set.Icc δ (Real.pi * h)) => (div_pos (lt_of_lt_of_le hδ0 hu.1) (by positivity)).ne')).neg).mul continuousOn_const
      have hle := intervalIntegral.integral_mono_on hδ_lt_pih.le
        ((hcont_diff.mono (Set.Icc_subset_Icc_right hpih_le_7h)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hδ_lt_pih.le)
        (hcont_ub.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hδ_lt_pih.le)
      have hpt : ∀ u ∈ Set.Icc δ (Real.pi * h),
          Real.log (u / (Real.pi * h)) * (sincSq (7 * h) - sincSq u) ≤
            (-Real.log (u / (Real.pi * h))) * ((7 * h) ^ 2 / 3) := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le hδ0 hu.1
        have hlog_np : Real.log (u / (Real.pi * h)) ≤ 0 :=
          Real.log_nonpos (by positivity) ((div_le_one (by positivity)).mpr hu.2)
        have hsu_le1 : sincSq u ≤ 1 := by
          unfold sincSq
          have h1 : |Real.sin u| ≤ |u| := Real.abs_sin_le_abs
          rw [abs_of_pos hu0] at h1
          have h2 : |Real.sin u / u| ≤ 1 := by rw [abs_div, abs_of_pos hu0, div_le_one hu0]; exact h1
          rw [← sq_abs]; nlinarith [abs_nonneg (Real.sin u / u)]
        have hdiff_ub : sincSq u - sincSq (7 * h) ≤ (7 * h) ^ 2 / 3 := by linarith
        nlinarith
      have hle' := hle hpt
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg,
          hlog_int hδ0 hδ_lt_pih.le] at hle'
      have hF_pih : F (Real.pi * h) = -(Real.pi * h) := by
        dsimp [F]; rw [div_self (by positivity), Real.log_one]; ring
      rw [hF_pih] at hle'
      have hneg_le : -(-(Real.pi * h) - F δ) ≤ Real.pi * h := by linarith
      exact le_trans hle' (mul_le_mul_of_nonneg_right hneg_le (by positivity))
    have htotal : (∫ u in δ..(7 * h), Real.log (u / (Real.pi * h)) * (sincSq (7 * h) - sincSq u)) ≤
        (Real.pi * h) * ((7 * h) ^ 2 / 3) := by linarith
    have hmul := mul_le_mul_of_nonneg_left htotal (by positivity : (0 : ℝ) ≤ 2 / (Real.pi * h))
    have hsimp : (2 / (Real.pi * h)) * ((Real.pi * h) * ((7 * h) ^ 2 / 3)) = 98 / 3 * h ^ 2 := by
      have hph' : Real.pi * h ≠ 0 := by positivity
      field_simp; ring
    rw [hsimp] at hmul
    nlinarith
  -- Paso 3: combinar en ∫_δ^{Th/2} f u du, extender a M = max 1 (Th/2) y aplicar las dos cotas universales
  set M : ℝ := max 1 (T * h / 2)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hTh_le_M : T * h / 2 ≤ M := le_max_right _ _
  have hδ_le_M : δ ≤ M := by linarith
  have hcomb_int :
      (∫ u in δ..(7 * h), f u) + (∫ u in (7 * h)..(T * h / 2), f u) ≤ ∫ u in δ..M, f u := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      ((hf_cont hδ0).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (le_trans hδ_lt_pih.le hpih_le_7h))
      ((hf_cont (by positivity)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) h7h_le_Th)
    rw [h1]
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      ((hf_cont hδ0).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (le_trans (le_trans hδ_lt_pih.le hpih_le_7h) h7h_le_Th))
      ((hf_cont (by positivity)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hTh_le_M)
    rw [← h2]
    have hnn : 0 ≤ ∫ u in (T * h / 2)..M, f u := by
      apply intervalIntegral.integral_nonneg hTh_le_M
      intro u hu
      dsimp [f]
      have hu_ge : Real.pi * h ≤ u := le_trans hpih_le_7h (le_trans h7h_le_Th hu.1)
      exact mul_nonneg (Real.log_nonneg ((one_le_div (by positivity)).mpr hu_ge)) (sincSq_nonneg u)
    linarith
  -- Separar f u = ln(1/(πh)) * sincSq u + ln u * sincSq u en [δ, M]
  have hsplit_f : (∫ u in δ..M, f u) =
      Real.log (1 / (Real.pi * h)) * (∫ u in δ..M, sincSq u) + (∫ u in δ..M, Real.log u * sincSq u) := by
    have heq : Set.EqOn f (fun u => Real.log (1 / (Real.pi * h)) * sincSq u + Real.log u * sincSq u)
        (Set.uIcc δ M) := by
      intro u hu
      rw [Set.uIcc_of_le hδ_le_M] at hu
      have hu0 : 0 < u := lt_of_lt_of_le hδ0 hu.1
      dsimp [f]
      have harg : u / (Real.pi * h) = (1 / (Real.pi * h)) * u := by ring
      rw [harg, Real.log_mul (by positivity) hu0.ne']; ring
    rw [intervalIntegral.integral_congr heq]
    have hs_contM : ContinuousOn sincSq (Set.Icc δ M) := by
      unfold sincSq
      exact (Real.continuous_sin.continuousOn.div continuousOn_id
        (fun u (hu : u ∈ Set.Icc δ M) => (lt_of_lt_of_le hδ0 hu.1).ne')).pow 2
    have hcont1 : ContinuousOn (fun u => Real.log (1 / (Real.pi * h)) * sincSq u) (Set.Icc δ M) :=
      continuousOn_const.mul hs_contM
    have hcont2 : ContinuousOn (fun u => Real.log u * sincSq u) (Set.Icc δ M) :=
      (Real.continuousOn_log.mono (fun u (hu : u ∈ Set.Icc δ M) => (lt_of_lt_of_le hδ0 hu.1).ne')).mul hs_contM
    rw [intervalIntegral.integral_add (hcont1.intervalIntegrable_of_Icc hδ_le_M)
        (hcont2.intervalIntegrable_of_Icc hδ_le_M), intervalIntegral.integral_const_mul]
  have hlog_pih_nn : 0 ≤ Real.log (1 / (Real.pi * h)) := by
    apply Real.log_nonneg
    rw [one_le_div (by positivity)]
    have hpi : Real.pi < 4 := lt_trans Real.pi_lt_d4 (by norm_num)
    nlinarith
  have hA := integral_sincSq_le_pi_div_two hδ0 hδ_le_M
  have hB := integral_log_mul_sincSq_le_zero hδ0 hδ_small hM1
  have hM_bound : (∫ u in δ..M, f u) ≤ Real.log (1 / (Real.pi * h)) * (Real.pi / 2) := by
    rw [hsplit_f]
    have h1 := mul_le_mul_of_nonneg_left hA hlog_pih_nn
    linarith
  have hfinal_mul : (2 / (Real.pi * h)) * (∫ u in δ..M, f u) ≤ (1 / h) * Real.log (1 / (Real.pi * h)) := by
    calc (2 / (Real.pi * h)) * (∫ u in δ..M, f u)
        ≤ (2 / (Real.pi * h)) * (Real.log (1 / (Real.pi * h)) * (Real.pi / 2)) :=
          mul_le_mul_of_nonneg_left hM_bound (by positivity)
      _ = (1 / h) * Real.log (1 / (Real.pi * h)) := by
          have hh' : h ≠ 0 := hh0.ne'
          have hpi' : Real.pi ≠ 0 := Real.pi_pos.ne'
          field_simp
  have hcomb_mul : (2 / (Real.pi * h)) * ((∫ u in δ..(7 * h), f u) + (∫ u in (7 * h)..(T * h / 2), f u)) ≤
      (2 / (Real.pi * h)) * (∫ u in δ..M, f u) :=
    mul_le_mul_of_nonneg_left hcomb_int (by positivity)
  rw [hsub_var]
  linarith

/-! ### Variación total de `sincSq` en `(0, π]` y en cada período `[kπ, (k+1)π]` (sin `sorry`) -/

/-- Integral de `|sincSqDeriv u|` en cualquier subintervalo `[a, b] ⊆ (0, π]`. -/
lemma integral_abs_sincSqDeriv_on_zero_pi {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    (∫ u in a..b, |sincSqDeriv u|) = sincSq a - sincSq b := by
  have hcont : ContinuousOn sincSqDeriv (Set.Icc a b) := by
    unfold sincSqDeriv
    have hne : ∀ u ∈ Set.Icc a b, u ≠ 0 := fun u hu => (lt_of_lt_of_le ha hu.1).ne'
    refine (continuousOn_const.mul (Real.continuous_sin.continuousOn.div continuousOn_id hne)).mul ?_
    refine ((continuousOn_id.mul Real.continuous_cos.continuousOn).sub
      Real.continuous_sin.continuousOn).div (continuousOn_id.pow 2) ?_
    intro u hu
    exact pow_ne_zero 2 (hne u hu)
  have heq : (∫ u in a..b, |sincSqDeriv u|) = ∫ u in a..b, -sincSqDeriv u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le hab] at hu
    have hu0 : 0 < u := lt_trans ha hu.1
    by_cases hupi : u < Real.pi
    · exact abs_of_nonpos (sincSqDeriv_nonpos_on_Ioo_zero_pi hu0 hupi)
    · have hEq : u = Real.pi := le_antisymm (le_trans hu.2 hb) (le_of_not_gt hupi)
      subst hEq
      simp [sincSqDeriv]
  rw [heq, intervalIntegral.integral_neg]
  have hftc : (∫ u in a..b, sincSqDeriv u) = sincSq b - sincSq a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [Set.uIcc_of_le hab] at hu
      exact sincSq_hasDerivAt (lt_of_lt_of_le ha hu.1).ne'
    · exact hcont.intervalIntegrable_of_Icc hab
  linarith

/-- Variación total exacta de `sincSq` en cada período `[kπ, (k+1)π]` (`k ≥ 1`):
    `∫_{kπ}^{(k+1)π} |sincSqDeriv u| du ≤ 2 / (1 + ((k + 3/8)π)²)`. -/
lemma sincSq_variation_on_period {k : ℕ} (hk : 1 ≤ k) :
    (∫ u in (k : ℝ) * Real.pi..((k + 1 : ℕ) : ℝ) * Real.pi, |sincSqDeriv u|) ≤
      2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2) := by
  set a : ℝ := (k : ℝ) * Real.pi
  set b : ℝ := ((k + 1 : ℕ) : ℝ) * Real.pi
  have ha_pos : 0 < a := by
    dsimp [a]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]; push_cast; linarith [Real.pi_pos]
  have hb_eq : b = a + Real.pi := by dsimp [a, b]; push_cast; ring
  set sgn : ℝ := (-1 : ℝ) ^ k
  have hsgn_sq : sgn * sgn = 1 := by
    dsimp [sgn]; rw [← sq, ← pow_mul, mul_comm, pow_mul]; norm_num
  -- Identidad de signo: sgn * sin(a + t) = sin t y sgn * cos(a + t) = cos t
  have hsin_shift : ∀ t : ℝ, sgn * Real.sin (a + t) = Real.sin t := by
    intro t
    have h1 : Real.sin (a + t) = Real.sin t * sgn := by
      dsimp [a, sgn]; rw [add_comm, Real.sin_add_nat_mul_pi]; ring
    rw [h1]
    calc sgn * (Real.sin t * sgn) = (sgn * sgn) * Real.sin t := by ring
      _ = Real.sin t := by rw [hsgn_sq, one_mul]
  have hcos_shift : ∀ t : ℝ, sgn * Real.cos (a + t) = Real.cos t := by
    intro t
    have h1 : Real.cos (a + t) = Real.cos t * sgn := by
      dsimp [a, sgn]; rw [add_comm, Real.cos_add_nat_mul_pi]; ring
    rw [h1]
    calc sgn * (Real.cos t * sgn) = (sgn * sgn) * Real.cos t := by ring
      _ = Real.cos t := by rw [hsgn_sq, one_mul]
  -- Función auxiliar h(u) = sgn * (u * cos u - sin u), estrictamente decreciente en [a, b]
  let hfun : ℝ → ℝ := fun u => sgn * (u * Real.cos u - Real.sin u)
  have hh_deriv : ∀ u : ℝ, HasDerivAt hfun (-(u * (sgn * Real.sin u))) u := by
    intro u
    have h2 : HasDerivAt hfun (sgn * (1 * Real.cos u + u * -Real.sin u - Real.cos u)) u :=
      (((hasDerivAt_id u).mul (Real.hasDerivAt_cos u)).sub (Real.hasDerivAt_sin u)).const_mul sgn
    have heq : sgn * (1 * Real.cos u + u * -Real.sin u - Real.cos u) = -(u * (sgn * Real.sin u)) := by
      ring
    rwa [heq] at h2
  have hh_anti : StrictAntiOn hfun (Set.Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b)
    · exact (continuous_const.mul ((continuous_id.mul Real.continuous_cos).sub Real.continuous_sin)).continuousOn
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hh_deriv u).deriv]
      have hu0 : 0 < u := lt_trans ha_pos hu.1
      have hsin_pos : 0 < sgn * Real.sin u := by
        have ht : u = a + (u - a) := by ring
        rw [ht, hsin_shift]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2, hb_eq])
      nlinarith
  -- Evaluamos hfun en c1 = a + 3π/8 (> 0) y c2 = a + π/2 (< 0)
  set c1 : ℝ := a + 3 * Real.pi / 8
  set c2 : ℝ := a + Real.pi / 2
  have hc1_pos : 0 < hfun c1 := by
    have hcos_lb : (0.35 : ℝ) < Real.cos (3 * Real.pi / 8) := by
      have h2mul : Real.cos (3 * Real.pi / 4) = 2 * Real.cos (3 * Real.pi / 8) ^ 2 - 1 := by
        rw [show (3 * Real.pi / 4 : ℝ) = 2 * (3 * Real.pi / 8) by ring, Real.cos_two_mul]
      have h34 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
        rw [show (3 * Real.pi / 4 : ℝ) = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub,
            Real.cos_pi_div_four]
      have hsq2 : Real.sqrt 2 < 1.42 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hcos_pos : 0 < Real.cos (3 * Real.pi / 8) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      nlinarith
    have hsin_le : Real.sin (3 * Real.pi / 8) ≤ 1 := Real.sin_le_one _
    have hc1_ge : (4.1 : ℝ) < c1 := by
      dsimp [c1, a]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith
    have hh_eq : hfun c1 = c1 * Real.cos (3 * Real.pi / 8) - Real.sin (3 * Real.pi / 8) := by
      dsimp [hfun, c1]
      rw [mul_sub, ← mul_assoc, mul_comm sgn, mul_assoc, hcos_shift, hsin_shift]
    rw [hh_eq]
    nlinarith
  have hc2_neg : hfun c2 < 0 := by
    have hh_eq : hfun c2 = c2 * Real.cos (Real.pi / 2) - Real.sin (Real.pi / 2) := by
      dsimp [hfun, c2]
      rw [mul_sub, ← mul_assoc, mul_comm sgn, mul_assoc, hcos_shift, hsin_shift]
    rw [hh_eq, Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num
  -- Por el Teorema del Valor Intermedio existe u_k ∈ [c1, c2] con hfun u_k = 0
  have hc12 : c1 ≤ c2 := by dsimp [c1, c2]; linarith [Real.pi_pos]
  have hcont_h : ContinuousOn hfun (Set.Icc c1 c2) :=
    (continuous_const.mul ((continuous_id.mul Real.continuous_cos).sub Real.continuous_sin)).continuousOn
  have h0_mem : (0 : ℝ) ∈ Set.Icc (hfun c2) (hfun c1) := ⟨hc2_neg.le, hc1_pos.le⟩
  rcases intermediate_value_Icc' hc12 hcont_h h0_mem with ⟨uk, huk_mem, huk_zero⟩
  have hauk : a ≤ uk := by dsimp [c1] at huk_mem; linarith [huk_mem.1, Real.pi_pos]
  have hukb : uk ≤ b := by dsimp [c2] at huk_mem; linarith [huk_mem.2, hb_eq, Real.pi_pos]
  -- Signo de sincSqDeriv en (a, uk) (≥ 0) y en (uk, b) (≤ 0)
  have hcont_d : ContinuousOn sincSqDeriv (Set.Icc a b) := by
    unfold sincSqDeriv
    have hne : ∀ u ∈ Set.Icc a b, u ≠ 0 := fun u hu => (lt_of_lt_of_le ha_pos hu.1).ne'
    refine (continuousOn_const.mul (Real.continuous_sin.continuousOn.div continuousOn_id hne)).mul ?_
    refine ((continuousOn_id.mul Real.continuous_cos.continuousOn).sub
      Real.continuous_sin.continuousOn).div (continuousOn_id.pow 2) ?_
    intro u hu
    exact pow_ne_zero 2 (hne u hu)
  have hpos_left : ∀ u ∈ Set.Ioo a uk, 0 ≤ sincSqDeriv u := by
    intro u hu
    have hu0 : 0 < u := lt_trans ha_pos hu.1
    have hsin_pos : 0 < sgn * Real.sin u := by
      have ht : u = a + (u - a) := by ring
      rw [ht, hsin_shift]
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2, hukb, hb_eq])
    have hh_pos : 0 < hfun u := by
      rw [← huk_zero]
      exact hh_anti ⟨hu.1.le, le_trans hu.2.le hukb⟩ ⟨hauk, hukb⟩ hu.2
    have hprod : 0 ≤ Real.sin u * (u * Real.cos u - Real.sin u) := by
      have h1 : (sgn * Real.sin u) * hfun u = Real.sin u * (u * Real.cos u - Real.sin u) := by
        dsimp [hfun]
        calc (sgn * Real.sin u) * (sgn * (u * Real.cos u - Real.sin u))
            = (sgn * sgn) * (Real.sin u * (u * Real.cos u - Real.sin u)) := by ring
          _ = Real.sin u * (u * Real.cos u - Real.sin u) := by rw [hsgn_sq, one_mul]
      rw [← h1]
      exact mul_nonneg hsin_pos.le hh_pos.le
    unfold sincSqDeriv
    have hrew : 2 * (Real.sin u / u) * ((u * Real.cos u - Real.sin u) / u ^ 2) =
        2 * (Real.sin u * (u * Real.cos u - Real.sin u)) / u ^ 3 := by ring
    rw [hrew]
    exact div_nonneg (by linarith) (by positivity)
  have hneg_right : ∀ u ∈ Set.Ioo uk b, sincSqDeriv u ≤ 0 := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha_pos (le_trans hauk hu.1.le)
    have hsin_pos : 0 < sgn * Real.sin u := by
      have ht : u = a + (u - a) := by ring
      rw [ht, hsin_shift]
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hu.1, hauk]) (by linarith [hu.2, hb_eq])
    have hh_neg : hfun u < 0 := by
      rw [← huk_zero]
      exact hh_anti ⟨hauk, hukb⟩ ⟨le_trans hauk hu.1.le, hu.2.le⟩ hu.1
    have hprod : Real.sin u * (u * Real.cos u - Real.sin u) ≤ 0 := by
      have h1 : (sgn * Real.sin u) * hfun u = Real.sin u * (u * Real.cos u - Real.sin u) := by
        dsimp [hfun]
        calc (sgn * Real.sin u) * (sgn * (u * Real.cos u - Real.sin u))
            = (sgn * sgn) * (Real.sin u * (u * Real.cos u - Real.sin u)) := by ring
          _ = Real.sin u * (u * Real.cos u - Real.sin u) := by rw [hsgn_sq, one_mul]
      rw [← h1]
      exact mul_nonpos_of_nonneg_of_nonpos hsin_pos.le hh_neg.le
    unfold sincSqDeriv
    have hrew : 2 * (Real.sin u / u) * ((u * Real.cos u - Real.sin u) / u ^ 2) =
        2 * (Real.sin u * (u * Real.cos u - Real.sin u)) / u ^ 3 := by ring
    rw [hrew]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  -- Partimos la integral en [a, uk] y [uk, b]
  have hsub_left : Set.Icc a uk ⊆ Set.Icc a b := fun u hu => ⟨hu.1, le_trans hu.2 hukb⟩
  have hsub_right : Set.Icc uk b ⊆ Set.Icc a b := fun u hu => ⟨le_trans hauk hu.1, hu.2⟩
  have hint_left : IntervalIntegrable (fun u => |sincSqDeriv u|) MeasureTheory.volume a uk :=
    (hcont_d.mono hsub_left).abs.intervalIntegrable_of_Icc hauk
  have hint_right : IntervalIntegrable (fun u => |sincSqDeriv u|) MeasureTheory.volume uk b :=
    (hcont_d.mono hsub_right).abs.intervalIntegrable_of_Icc hukb
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_left hint_right]
  have hI_left : (∫ u in a..uk, |sincSqDeriv u|) = sincSq uk := by
    have heq : (∫ u in a..uk, |sincSqDeriv u|) = ∫ u in a..uk, sincSqDeriv u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with u hu
      rw [Set.uIoc_of_le hauk] at hu
      by_cases hEq : u = uk
      · rw [hEq]
        have hzero : uk * Real.cos uk - Real.sin uk = 0 := by
          have : sgn * (uk * Real.cos uk - Real.sin uk) = 0 := huk_zero
          have h1 := congrArg (sgn * ·) this
          rw [← mul_assoc, hsgn_sq, one_mul, mul_zero] at h1
          exact h1
        simp [sincSqDeriv, hzero]
      · exact abs_of_nonneg (hpos_left u ⟨hu.1, lt_of_le_of_ne hu.2 hEq⟩)
    rw [heq]
    have hftc : (∫ u in a..uk, sincSqDeriv u) = sincSq uk - sincSq a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro u hu
        rw [Set.uIcc_of_le hauk] at hu
        exact sincSq_hasDerivAt (lt_of_lt_of_le ha_pos hu.1).ne'
      · exact (hcont_d.mono hsub_left).intervalIntegrable_of_Icc hauk
    have hsa : sincSq a = 0 := by
      unfold sincSq; dsimp [a]; rw [Real.sin_nat_mul_pi]; simp
    rw [hftc, hsa, sub_zero]
  have hI_right : (∫ u in uk..b, |sincSqDeriv u|) = sincSq uk := by
    have heq : (∫ u in uk..b, |sincSqDeriv u|) = ∫ u in uk..b, -sincSqDeriv u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with u hu
      rw [Set.uIoc_of_le hukb] at hu
      by_cases hEq : u = b
      · rw [hEq]
        have hsinb : Real.sin b = 0 := by dsimp [b]; exact Real.sin_nat_mul_pi (k + 1)
        simp [sincSqDeriv, hsinb]
      · exact abs_of_nonpos (hneg_right u ⟨hu.1, lt_of_le_of_ne hu.2 hEq⟩)
    rw [heq, intervalIntegral.integral_neg]
    have hftc : (∫ u in uk..b, sincSqDeriv u) = sincSq b - sincSq uk := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro u hu
        rw [Set.uIcc_of_le hukb] at hu
        exact sincSq_hasDerivAt (lt_of_lt_of_le ha_pos (le_trans hauk hu.1)).ne'
      · exact (hcont_d.mono hsub_right).intervalIntegrable_of_Icc hukb
    have hsb : sincSq b = 0 := by
      unfold sincSq; dsimp [b]; rw [Real.sin_nat_mul_pi]; simp
    rw [hftc, hsb]; ring
  rw [hI_left, hI_right]
  -- Cota exacta sincSq(uk) = 1 / (1 + uk²) ≤ 1 / (1 + ((k + 3/8)π)²)
  have huk_eq : uk * Real.cos uk = Real.sin uk := by
    have : sgn * (uk * Real.cos uk - Real.sin uk) = 0 := huk_zero
    have h1 := congrArg (sgn * ·) this
    rw [← mul_assoc, hsgn_sq, one_mul, mul_zero] at h1
    linarith
  have huk_pos : 0 < uk := lt_of_lt_of_le ha_pos hauk
  have hsinc_uk : sincSq uk = 1 / (1 + uk ^ 2) := by
    unfold sincSq
    rw [div_pow, eq_div_iff (by positivity)]
    have htrig : Real.sin uk ^ 2 + Real.cos uk ^ 2 = 1 := Real.sin_sq_add_cos_sq uk
    have h1 : Real.sin uk ^ 2 * (1 + uk ^ 2) = uk ^ 2 * (Real.sin uk ^ 2 + Real.cos uk ^ 2) := by
      calc Real.sin uk ^ 2 * (1 + uk ^ 2)
          = Real.sin uk ^ 2 + uk ^ 2 * Real.sin uk ^ 2 := by ring
        _ = (uk * Real.cos uk) ^ 2 + uk ^ 2 * Real.sin uk ^ 2 := by rw [← huk_eq]
        _ = uk ^ 2 * (Real.sin uk ^ 2 + Real.cos uk ^ 2) := by ring
    rw [div_mul_eq_mul_div, h1, htrig, mul_one, div_self (pow_ne_zero 2 huk_pos.ne')]
  have hc1_eq : c1 = ((k : ℝ) + 3 / 8) * Real.pi := by dsimp [c1, a]; ring
  have huk_ge : ((k : ℝ) + 3 / 8) * Real.pi ≤ uk := by rw [← hc1_eq]; exact huk_mem.1
  rw [hsinc_uk]
  have hc1_nonneg : 0 ≤ ((k : ℝ) + 3 / 8) * Real.pi := by positivity
  have hsq_le : (((k : ℝ) + 3 / 8) * Real.pi) ^ 2 ≤ uk ^ 2 := by nlinarith
  have h1 : 1 / (1 + uk ^ 2) ≤ 1 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : 2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2) =
      2 * (1 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) := by ring
  linarith

/-- Cota elemental de la cola `S0`: `∑_{k=1}^{K-1} 2 / (1 + ((k + 3/8)π)²) ≤ 0.2126`. -/
lemma sum_period_S0_le (K : ℕ) :
    ∑ k ∈ Finset.Ico 1 K, (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) ≤ 0.2126 := by
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hterm_le : ∀ k : ℕ, 1 ≤ k →
      2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2) ≤
        2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2) := by
    intro k _
    have hc : 0 ≤ (k : ℝ) + 3 / 8 := by positivity
    have hmul : ((k : ℝ) + 3 / 8) * 3.1415 ≤ ((k : ℝ) + 3 / 8) * Real.pi :=
      mul_le_mul_of_nonneg_left hpi.le hc
    have hsq : (((k : ℝ) + 3 / 8) * 3.1415) ^ 2 ≤ (((k : ℝ) + 3 / 8) * Real.pi) ^ 2 := by
      nlinarith [mul_nonneg hc (by norm_num : (0 : ℝ) ≤ 3.1415)]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  -- Suma telescópica para k ≥ 4: 2 / (1 + ((k + 3/8)*3.1415)²) ≤ (2 / 3.1415²) * (1/(k - 1/2) - 1/(k + 1/2))
  have htele_step : ∀ k : ℕ, 4 ≤ k →
      2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2) ≤
        (2 / 3.1415 ^ 2) * (1 / ((k : ℝ) - 1 / 2) - 1 / ((k : ℝ) + 1 / 2)) := by
    intro k hk
    have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hpos_m : (0 : ℝ) < (k : ℝ) - 1 / 2 := by linarith
    have hpos_p : (0 : ℝ) < (k : ℝ) + 1 / 2 := by linarith
    have hdiff : 1 / ((k : ℝ) - 1 / 2) - 1 / ((k : ℝ) + 1 / 2) =
        1 / (((k : ℝ) - 1 / 2) * ((k : ℝ) + 1 / 2)) := by
      have h1 : (k : ℝ) - 1 / 2 ≠ 0 := hpos_m.ne'
      have h2 : (k : ℝ) + 1 / 2 ≠ 0 := hpos_p.ne'
      rw [div_sub_div _ _ h1 h2]; ring
    rw [hdiff]
    have hden : ((k : ℝ) - 1 / 2) * ((k : ℝ) + 1 / 2) * 3.1415 ^ 2 ≤
        1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2 := by nlinarith
    have hrew : (2 / 3.1415 ^ 2) * (1 / (((k : ℝ) - 1 / 2) * ((k : ℝ) + 1 / 2))) =
        2 / (((k : ℝ) - 1 / 2) * ((k : ℝ) + 1 / 2) * 3.1415 ^ 2) := by
      rw [div_mul_div_comm, mul_one, mul_comm (3.1415 ^ 2)]
    rw [hrew]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  have htele_sum : ∀ M : ℕ, 4 ≤ M →
      ∑ k ∈ Finset.Ico 4 M, (1 / ((k : ℝ) - 1 / 2) - 1 / ((k : ℝ) + 1 / 2)) ≤ 1 / 3.5 := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp; norm_num
    | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm]
      have htele_exact : ∀ n : ℕ, 4 ≤ n →
          ∑ k ∈ Finset.Ico 4 n, (1 / ((k : ℝ) - 1 / 2) - 1 / ((k : ℝ) + 1 / 2)) =
            1 / 3.5 - 1 / ((n : ℝ) - 1 / 2) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => simp; norm_num
        | succ r hr ihr =>
          rw [Finset.sum_Ico_succ_top hr, ihr]
          push_cast; ring
      rw [htele_exact m hm]
      have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hpos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by linarith
      have : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1 / 2) := by positivity
      linarith
  have hmono_K :
      ∑ k ∈ Finset.Ico 1 K, (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) ≤
        ∑ k ∈ Finset.Ico 1 (max K 4), (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_right (le_max_left K 4)) (fun _ _ _ => by positivity)
  have hsplit : Finset.Ico 1 (max K 4) = Finset.Ico (1 : ℕ) 4 ∪ Finset.Ico 4 (max K 4) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ico (1 : ℕ) 4) (Finset.Ico 4 (max K 4)) := by
    rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  have hhead :
      ∑ k ∈ Finset.Ico (1 : ℕ) 4, (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) ≤ 0.15467 := by
    have h1 : ∑ k ∈ Finset.Ico (1 : ℕ) 4, (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) ≤
        ∑ k ∈ Finset.Ico (1 : ℕ) 4, (2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2)) :=
      Finset.sum_le_sum (fun k hk => hterm_le k (Finset.mem_Ico.mp hk).1)
    have h2 : ∑ k ∈ Finset.Ico (1 : ℕ) 4, (2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2)) ≤ 0.15467 := by
      have hico : Finset.Ico (1 : ℕ) 4 = {1, 2, 3} := by decide
      rw [hico]
      norm_num
    exact le_trans h1 h2
  have htail :
      ∑ k ∈ Finset.Ico 4 (max K 4), (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) ≤ 0.05793 := by
    calc ∑ k ∈ Finset.Ico 4 (max K 4), (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2))
        ≤ ∑ k ∈ Finset.Ico 4 (max K 4),
            (2 / 3.1415 ^ 2) * (1 / ((k : ℝ) - 1 / 2) - 1 / ((k : ℝ) + 1 / 2)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk4 : 4 ≤ k := (Finset.mem_Ico.mp hk).1
          exact le_trans (hterm_le k (by omega)) (htele_step k hk4)
      _ = (2 / 3.1415 ^ 2) * ∑ k ∈ Finset.Ico 4 (max K 4),
            (1 / ((k : ℝ) - 1 / 2) - 1 / ((k : ℝ) + 1 / 2)) := by
          rw [← Finset.mul_sum]
      _ ≤ (2 / 3.1415 ^ 2) * (1 / 3.5) :=
          mul_le_mul_of_nonneg_left (htele_sum (max K 4) (le_max_right K 4)) (by positivity)
      _ ≤ 0.05793 := by norm_num
  calc ∑ k ∈ Finset.Ico 1 K, (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2))
      ≤ ∑ k ∈ Finset.Ico 1 (max K 4), (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) := hmono_K
    _ = (∑ k ∈ Finset.Ico (1 : ℕ) 4, (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2))) +
        (∑ k ∈ Finset.Ico 4 (max K 4), (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2))) := by
        rw [hsplit, Finset.sum_union hdisj]
    _ ≤ 0.15467 + 0.05793 := add_le_add hhead htail
    _ = 0.2126 := by norm_num

/-- Cota elemental de la cola logarítmica `S1`:
    `∑_{k=1}^{K-1} (2 / (1 + ((k + 3/8)π)²)) * ln((k+1)π) ≤ 0.52`. -/
lemma sum_period_S1_le (K : ℕ) :
    ∑ k ∈ Finset.Ico 1 K,
      (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)
    ≤ 0.52 := by
  have hpi_lb : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_ub : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have he_lb : (2.71828 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
  -- Cotas de logaritmos pequeños vía e^a ≥ x
  have hlog_le_of_pow : ∀ (x a : ℝ) (p q : ℕ), 0 < x → 0 < q → a * (q : ℝ) = (p : ℝ) →
      x ^ q ≤ (2.71828 : ℝ) ^ p → Real.log x ≤ a := by
    intro x a p q hx hq ha hpow
    rw [Real.log_le_iff_le_exp hx]
    have h1 : (Real.exp a) ^ q = (Real.exp 1) ^ p := by
      rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul, mul_one, mul_comm, ha]
    have h2 : x ^ q ≤ (Real.exp a) ^ q := by
      rw [h1]
      exact le_trans hpow (by gcongr)
    by_contra hcon
    push Not at hcon
    have : (Real.exp a) ^ q < x ^ q := by gcongr
    linarith
  have hterm_le : ∀ k : ℕ, 1 ≤ k →
      (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi) ≤
        (2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * 3.1416) := by
    intro k hk
    have hc : 0 ≤ (k : ℝ) + 3 / 8 := by positivity
    have hmul : ((k : ℝ) + 3 / 8) * 3.1415 ≤ ((k : ℝ) + 3 / 8) * Real.pi :=
      mul_le_mul_of_nonneg_left hpi_lb.le hc
    have hsq : (((k : ℝ) + 3 / 8) * 3.1415) ^ 2 ≤ (((k : ℝ) + 3 / 8) * Real.pi) ^ 2 := by
      nlinarith [mul_nonneg hc (by norm_num : (0 : ℝ) ≤ 3.1415)]
    have h1 : 2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2) ≤
        2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have h2 : Real.log (((k + 1 : ℕ) : ℝ) * Real.pi) ≤ Real.log (((k + 1 : ℕ) : ℝ) * 3.1416) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hpi_ub.le (by positivity))
    have hlog_nonneg : 0 ≤ Real.log (((k + 1 : ℕ) : ℝ) * Real.pi) := by
      apply Real.log_nonneg
      have : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
      nlinarith
    exact mul_le_mul h1 h2 hlog_nonneg (by positivity)
  -- Cabeza k = 1..5
  have hhead :
      ∑ k ∈ Finset.Ico (1 : ℕ) 6,
        (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)
      ≤ 0.3612 := by
    have h1 : ∑ k ∈ Finset.Ico (1 : ℕ) 6,
          (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi) ≤
        ∑ k ∈ Finset.Ico (1 : ℕ) 6,
          (2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * 3.1416) :=
      Finset.sum_le_sum (fun k hk => hterm_le k (Finset.mem_Ico.mp hk).1)
    have hl2 : Real.log ((2 : ℝ) * 3.1416) ≤ 1.84 :=
      hlog_le_of_pow _ 1.84 46 25 (by norm_num) (by omega) (by norm_num) (by norm_num)
    have hl3 : Real.log ((3 : ℝ) * 3.1416) ≤ 2.25 :=
      hlog_le_of_pow _ 2.25 9 4 (by norm_num) (by omega) (by norm_num) (by norm_num)
    have hl4 : Real.log ((4 : ℝ) * 3.1416) ≤ 2.54 :=
      hlog_le_of_pow _ 2.54 127 50 (by norm_num) (by omega) (by norm_num) (by norm_num)
    have hl5 : Real.log ((5 : ℝ) * 3.1416) ≤ 2.76 :=
      hlog_le_of_pow _ 2.76 69 25 (by norm_num) (by omega) (by norm_num) (by norm_num)
    have hl6 : Real.log ((6 : ℝ) * 3.1416) ≤ 2.94 :=
      hlog_le_of_pow _ 2.94 147 50 (by norm_num) (by omega) (by norm_num) (by norm_num)
    have hico : Finset.Ico (1 : ℕ) 6 = {1, 2, 3, 4, 5} := by decide
    have h2 : ∑ k ∈ Finset.Ico (1 : ℕ) 6,
          (2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * 3.1416)
        ≤ 0.3612 := by
      rw [hico]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
        Nat.reduceEqDiff, or_self, not_false_eq_true]
      norm_num
      nlinarith
    exact le_trans h1 h2
  -- Cola k ≥ 6 vía telescópica F(u) = (ln u + 2.3) / u
  let F : ℝ → ℝ := fun u => (Real.log u + 2.3) / u
  have hF_step : ∀ k : ℕ, 6 ≤ k →
      (Real.log (k : ℝ) + 1.3) / (k : ℝ) ^ 2 ≤ F ((k : ℝ) - 1) - F (k : ℝ) := by
    intro k hk
    have hkR : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkm1 : (5 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    have hF_deriv : ∀ u ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ),
        HasDerivAt F (-((Real.log u + 1.3) / u ^ 2)) u := by
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      have hnum : HasDerivAt (fun x : ℝ => Real.log x + 2.3) (1 / u) u := by
        simpa using (Real.hasDerivAt_log hu0.ne').add_const 2.3
      have hdiv : HasDerivAt F (((1 / u) * u - (Real.log u + 2.3) * 1) / u ^ 2) u :=
        hnum.div (hasDerivAt_id u) hu0.ne'
      have heq : ((1 / u) * u - (Real.log u + 2.3) * 1) / u ^ 2 = -((Real.log u + 1.3) / u ^ 2) := by
        field_simp; ring
      rwa [heq] at hdiv
    have hcont : ContinuousOn (fun u : ℝ => (Real.log u + 1.3) / u ^ 2)
        (Set.Icc ((k : ℝ) - 1) (k : ℝ)) := by
      have hne : ∀ u ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ), u ≠ 0 := fun u hu => by linarith [hu.1]
      exact ((Real.continuousOn_log.mono (fun u hu => hne u hu)).add continuousOn_const).div
        (continuousOn_id.pow 2) (fun u hu => pow_ne_zero 2 (hne u hu))
    have hftc : (∫ u in ((k : ℝ) - 1)..(k : ℝ), (Real.log u + 1.3) / u ^ 2) =
        F ((k : ℝ) - 1) - F (k : ℝ) := by
      have hneg : (∫ u in ((k : ℝ) - 1)..(k : ℝ), -((Real.log u + 1.3) / u ^ 2)) =
          F (k : ℝ) - F ((k : ℝ) - 1) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro u hu
          rw [Set.uIcc_of_le (by linarith)] at hu
          exact hF_deriv u hu
        · exact hcont.neg.intervalIntegrable_of_Icc (by linarith)
      rw [intervalIntegral.integral_neg] at hneg
      linarith
    rw [← hftc]
    have hanti : AntitoneOn (fun u : ℝ => (Real.log u + 1.3) / u ^ 2)
        (Set.Icc ((k : ℝ) - 1) (k : ℝ)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont
      · intro u hu
        rw [interior_Icc] at hu
        have hu0 : 0 < u := by linarith [hu.1]
        have hnum : HasDerivAt (fun x : ℝ => Real.log x + 1.3) (1 / u) u := by
          simpa using (Real.hasDerivAt_log hu0.ne').add_const 1.3
        have hden : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
          simpa using hasDerivAt_pow 2 u
        have hdiv : HasDerivAt (fun x : ℝ => (Real.log x + 1.3) / x ^ 2)
            ((1 / u * u ^ 2 - (Real.log u + 1.3) * (2 * u)) / (u ^ 2) ^ 2) u :=
          hnum.div hden (pow_ne_zero 2 hu0.ne')
        exact hdiv.differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hu0 : 0 < u := by linarith [hu.1]
        have hnum : HasDerivAt (fun x : ℝ => Real.log x + 1.3) (1 / u) u := by
          simpa using (Real.hasDerivAt_log hu0.ne').add_const 1.3
        have hden : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
          simpa using hasDerivAt_pow 2 u
        have hdiv : HasDerivAt (fun x : ℝ => (Real.log x + 1.3) / x ^ 2)
            ((1 / u * u ^ 2 - (Real.log u + 1.3) * (2 * u)) / (u ^ 2) ^ 2) u :=
          hnum.div hden (pow_ne_zero 2 hu0.ne')
        rw [hdiv.deriv]
        have hlog5 : (1 : ℝ) ≤ Real.log u := by
          rw [Real.le_log_iff_exp_le hu0]; linarith [Real.exp_one_lt_d9, hu.1]
        have hnum_neg : (1 / u) * u ^ 2 - (Real.log u + 1.3) * (2 * u) ≤ 0 := by
          have : (1 / u) * u ^ 2 = u := by field_simp
          rw [this]
          nlinarith
        exact div_nonpos_of_nonpos_of_nonneg hnum_neg (sq_nonneg _)
    have hconst_le :
        (∫ _u in ((k : ℝ) - 1)..(k : ℝ), (Real.log (k : ℝ) + 1.3) / (k : ℝ) ^ 2) ≤
          ∫ u in ((k : ℝ) - 1)..(k : ℝ), (Real.log u + 1.3) / u ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hcont.intervalIntegrable_of_Icc (by linarith))
      intro u hu
      exact hanti hu ⟨by linarith, le_rfl⟩ hu.2
    simpa using hconst_le
  have hlog_shift : ∀ k : ℕ, 6 ≤ k →
      Real.log (((k + 1 : ℕ) : ℝ) * 3.1416) ≤ Real.log (k : ℝ) + 1.3 := by
    intro k hk
    have hkR : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h13 : Real.log ((7 / 6 : ℝ) * 3.1416) ≤ 1.3 :=
      hlog_le_of_pow _ 1.3 13 10 (by norm_num) (by omega) (by norm_num) (by norm_num)
    have hmul_le : ((k + 1 : ℕ) : ℝ) * 3.1416 ≤ (k : ℝ) * ((7 / 6 : ℝ) * 3.1416) := by
      push_cast; nlinarith
    calc Real.log (((k + 1 : ℕ) : ℝ) * 3.1416)
        ≤ Real.log ((k : ℝ) * ((7 / 6 : ℝ) * 3.1416)) :=
          Real.log_le_log (by positivity) hmul_le
      _ = Real.log (k : ℝ) + Real.log ((7 / 6 : ℝ) * 3.1416) :=
          Real.log_mul (by linarith) (by norm_num)
      _ ≤ Real.log (k : ℝ) + 1.3 := by linarith
  have htail_sum : ∀ M : ℕ, 6 ≤ M →
      ∑ k ∈ Finset.Ico 6 M, (F ((k : ℝ) - 1) - F (k : ℝ)) ≤ F 5 := by
    intro M hM
    have hexact : ∀ n : ℕ, 6 ≤ n →
        ∑ k ∈ Finset.Ico 6 n, (F ((k : ℝ) - 1) - F (k : ℝ)) = F 5 - F ((n : ℝ) - 1) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => simp; norm_num
      | succ r hr ihr =>
        rw [Finset.sum_Ico_succ_top hr, ihr]
        rw [show ((r + 1 : ℕ) : ℝ) - 1 = (r : ℝ) by push_cast; ring]
        ring
    rw [hexact M hM]
    have hM5 : (5 : ℝ) ≤ (M : ℝ) - 1 := by
      have : (6 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have hF_nonneg : 0 ≤ F ((M : ℝ) - 1) := by
      dsimp [F]
      have hlog_nonneg : 0 ≤ Real.log ((M : ℝ) - 1) := Real.log_nonneg (by linarith)
      positivity
    linarith
  have hF5 : F 5 ≤ 0.782 := by
    dsimp [F]
    have hl5 : Real.log 5 ≤ 1.61 :=
      hlog_le_of_pow 5 1.61 161 100 (by norm_num) (by omega) (by norm_num) (by norm_num)
    linarith
  have htail :
      ∑ k ∈ Finset.Ico 6 (max K 6),
        (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)
      ≤ 0.1586 := by
    calc ∑ k ∈ Finset.Ico 6 (max K 6),
            (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)
        ≤ ∑ k ∈ Finset.Ico 6 (max K 6),
            (2 / 3.1415 ^ 2) * (F ((k : ℝ) - 1) - F (k : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk6 : 6 ≤ k := (Finset.mem_Ico.mp hk).1
          have hkR : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk6
          have h1 := hterm_le k (by omega)
          have h2 : 2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2) ≤
              (2 / 3.1415 ^ 2) / (k : ℝ) ^ 2 := by
            rw [div_div]
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
          have h3 := hlog_shift k hk6
          have hlog_nn : 0 ≤ Real.log (((k + 1 : ℕ) : ℝ) * 3.1416) := by
            apply Real.log_nonneg; push_cast; nlinarith
          have h4 := mul_le_mul h2 h3 hlog_nn (by positivity)
          have h5 := hF_step k hk6
          calc (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)
              ≤ (2 / (1 + (((k : ℝ) + 3 / 8) * 3.1415) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * 3.1416) := h1
            _ ≤ ((2 / 3.1415 ^ 2) / (k : ℝ) ^ 2) * (Real.log (k : ℝ) + 1.3) := h4
            _ = (2 / 3.1415 ^ 2) * ((Real.log (k : ℝ) + 1.3) / (k : ℝ) ^ 2) := by ring
            _ ≤ (2 / 3.1415 ^ 2) * (F ((k : ℝ) - 1) - F (k : ℝ)) :=
                mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = (2 / 3.1415 ^ 2) * ∑ k ∈ Finset.Ico 6 (max K 6), (F ((k : ℝ) - 1) - F (k : ℝ)) := by
          rw [← Finset.mul_sum]
      _ ≤ (2 / 3.1415 ^ 2) * 0.782 :=
          mul_le_mul_of_nonneg_left (le_trans (htail_sum (max K 6) (le_max_right K 6)) hF5) (by positivity)
      _ ≤ 0.1586 := by norm_num
  have hmono_K :
      ∑ k ∈ Finset.Ico 1 K,
        (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)
      ≤ ∑ k ∈ Finset.Ico 1 (max K 6),
        (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (le_max_left K 6))
    intro k hk _
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hlog_nn : 0 ≤ Real.log (((k + 1 : ℕ) : ℝ) * Real.pi) := by
      apply Real.log_nonneg
      have : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
      nlinarith
    positivity
  have hsplit : Finset.Ico 1 (max K 6) = Finset.Ico (1 : ℕ) 6 ∪ Finset.Ico 6 (max K 6) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ico (1 : ℕ) 6) (Finset.Ico 6 (max K 6)) := by
    rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  calc ∑ k ∈ Finset.Ico 1 K,
          (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)
      ≤ ∑ k ∈ Finset.Ico 1 (max K 6),
          (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi) := hmono_K
    _ = (∑ k ∈ Finset.Ico (1 : ℕ) 6,
          (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)) +
        (∑ k ∈ Finset.Ico 6 (max K 6),
          (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)) := by
        rw [hsplit, Finset.sum_union hdisj]
    _ ≤ 0.3612 + 0.1586 := add_le_add hhead htail
    _ ≤ 0.52 := by norm_num

set_option maxHeartbeats 800000 in
/-- Cota del término integral de error `R(t) = N(t) - M(t)` de Trudgian contra `(sinc²)'`. -/
lemma sincSq_err_integral_bound {h T : ℝ} (hh0 : 0 < h) (hh2 : h < 0.02) (hT : 14 ≤ T)
    (hRvM : ∀ t : ℝ, Real.exp 1 ≤ t →
      |(zeroCount t : ℝ) - rvmMainTerm t| ≤
        0.112 * Real.log t + 0.278 * Real.log (Real.log t) + 2.51) :
    -2 * (∫ t in (14 : ℝ)..T, ((zeroCount t : ℝ) - rvmMainTerm t) * ((h / 2) * sincSqDeriv (t * h / 2)))
      ≤ 0.36 * Real.log (2 / h) + 7.17 := by
  let Rtrud : ℝ → ℝ := fun t => 0.112 * Real.log t + 0.278 * Real.log (Real.log t) + 2.51
  have he_lt_14 : Real.exp 1 < 14 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hRtrud_mono : ∀ {x y : ℝ}, Real.exp 1 ≤ x → x ≤ y → Rtrud x ≤ Rtrud y := by
    intro x y hx hxy
    have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
    have hlogx_ge : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hx
    have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log hx_pos hxy
    have hloglog_le : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
      Real.log_le_log (by linarith) hlog_le
    dsimp [Rtrud]
    linarith
  have hRtrud_nonneg : ∀ {x : ℝ}, Real.exp 1 ≤ x → 0 ≤ Rtrud x := by
    intro x hx
    have hlogx_ge : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hx
    have hloglog_nn : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlogx_ge
    dsimp [Rtrud]
    linarith
  have hRtrud_cont : ∀ {a b : ℝ}, Real.exp 1 ≤ a → ContinuousOn Rtrud (Set.Icc a b) := by
    intro a b ha
    have hlog_cont : ContinuousOn Real.log (Set.Icc a b) :=
      Real.continuousOn_log.mono (fun x hx => (lt_of_lt_of_le (Real.exp_pos 1) (le_trans ha hx.1)).ne')
    have hloglog_cont : ContinuousOn (fun x => Real.log (Real.log x)) (Set.Icc a b) := by
      refine Real.continuousOn_log.comp hlog_cont ?_
      intro x hx
      have h1 : 1 ≤ Real.log x := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (le_trans ha hx.1)
      exact (by linarith : (0 : ℝ) < Real.log x).ne'
    exact ((continuousOn_const.mul hlog_cont).add (continuousOn_const.mul hloglog_cont)).add continuousOn_const
  -- Paso 1: acotar -∫_{14}^T R(t) f'(t) dt ≤ ∫_{14}^T Rtrud(t) |f'(t)| dt
  let f' : ℝ → ℝ := fun t => (h / 2) * sincSqDeriv (t * h / 2)
  have hf'_cont : ContinuousOn f' (Set.Icc 14 T) := sincSq_scaled_deriv_continuousOn hh0
  have hf'_int : IntervalIntegrable f' MeasureTheory.volume 14 T :=
    hf'_cont.intervalIntegrable_of_Icc hT
  have hM_cont : ContinuousOn rvmMainTerm (Set.Icc 14 T) := by
    unfold rvmMainTerm
    refine (continuousOn_id.div_const _).mul ?_
    refine Real.continuousOn_log.comp (continuousOn_id.div_const _) ?_
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hden : 0 < 2 * Real.pi * Real.exp 1 := by positivity
    exact (div_pos ht0 hden).ne'
  have hMf'_int : IntervalIntegrable (fun t => rvmMainTerm t * f' t) MeasureTheory.volume 14 T :=
    (hM_cont.mul hf'_cont).intervalIntegrable_of_Icc hT
  have hNf'_int : IntervalIntegrable (fun t => (zeroCount t : ℝ) * f' t) MeasureTheory.volume 14 T := by
    have hN_mono : Monotone (fun t : ℝ => (zeroCount t : ℝ)) :=
      fun a b hab => Nat.cast_le.mpr (zeroCount_mono hab)
    have hN_int : IntervalIntegrable (fun t => (zeroCount t : ℝ)) MeasureTheory.volume 14 T :=
      hN_mono.intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    rcases (isCompact_Icc (a := (14 : ℝ)) (b := T)).exists_bound_of_continuousOn hf'_cont with ⟨C, hC⟩
    refine MeasureTheory.Integrable.mono' (hN_int.1.norm.const_mul (max C 0)) ?_ ?_
    · exact (hN_int.1.aestronglyMeasurable).mul (hf'_int.1.aestronglyMeasurable)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (le_trans (hC t ⟨ht.1.le, ht.2⟩) (le_max_left _ _)) (norm_nonneg _)
  have hRf'_int : IntervalIntegrable (fun t => -(((zeroCount t : ℝ) - rvmMainTerm t) * f' t))
      MeasureTheory.volume 14 T := by
    have hrew : (fun t => -(((zeroCount t : ℝ) - rvmMainTerm t) * f' t)) =
        (fun t => rvmMainTerm t * f' t - (zeroCount t : ℝ) * f' t) := by ext t; ring
    rw [hrew]
    exact hMf'_int.sub hNf'_int
  have hRtrud_f'_cont : ContinuousOn (fun t => Rtrud t * |f' t|) (Set.Icc 14 T) :=
    (hRtrud_cont he_lt_14.le).mul hf'_cont.abs
  have hRtrud_f'_int : IntervalIntegrable (fun t => Rtrud t * |f' t|) MeasureTheory.volume 14 T :=
    hRtrud_f'_cont.intervalIntegrable_of_Icc hT
  have hstep1 :
      -(∫ t in (14 : ℝ)..T, ((zeroCount t : ℝ) - rvmMainTerm t) * f' t) ≤
        ∫ t in (14 : ℝ)..T, Rtrud t * |f' t| := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_mono_on hT hRf'_int hRtrud_f'_int
    intro t ht
    have ht_ge : Real.exp 1 ≤ t := le_trans he_lt_14.le ht.1
    have h1 : -(((zeroCount t : ℝ) - rvmMainTerm t) * f' t) ≤
        |((zeroCount t : ℝ) - rvmMainTerm t) * f' t| := neg_le_abs _
    rw [abs_mul] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right (hRvM t ht_ge) (abs_nonneg _))
  -- Paso 2: cambio de variable u = t * (h / 2)
  let g : ℝ → ℝ := fun u => Rtrud (2 * u / h) * |sincSqDeriv u|
  have hsub_var :
      (∫ t in (14 : ℝ)..T, Rtrud t * |f' t|) = ∫ u in (7 * h)..(T * h / 2), g u := by
    have hrew : (fun t => Rtrud t * |f' t|) =
        (fun t => (h / 2) * g (t * (h / 2))) := by
      ext t
      dsimp [f', g]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < h / 2)]
      have harg1 : 2 * (t * (h / 2)) / h = t := by field_simp
      have harg2 : t * (h / 2) = t * h / 2 := by ring
      rw [harg1, harg2]; ring
    rw [hrew, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_right (f := g) (c := h / 2) (by positivity)]
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity : (h / 2 : ℝ) ≠ 0), one_mul]
    have ha : (14 : ℝ) * (h / 2) = 7 * h := by ring
    have hb : T * (h / 2) = T * h / 2 := by ring
    rw [ha, hb]
  -- Continuidad y no negatividad de g en [7h, M] para cualquier M
  have hg_cont : ∀ {a b : ℝ}, 7 * h ≤ a → ContinuousOn g (Set.Icc a b) := by
    intro a b ha
    have hlin : ContinuousOn (fun u : ℝ => 2 * u / h) (Set.Icc a b) :=
      (continuousOn_const.mul continuousOn_id).div_const h
    have hR_comp : ContinuousOn (fun u : ℝ => Rtrud (2 * u / h)) (Set.Icc a b) := by
      refine (hRtrud_cont (a := 14) (b := max 14 (2 * b / h)) he_lt_14.le).comp hlin ?_
      intro u hu
      constructor
      · have h1 : 14 = 2 * (7 * h) / h := by field_simp; ring
        rw [h1]
        exact div_le_div_of_nonneg_right (by linarith [ha, hu.1]) hh0.le
      · exact le_trans (div_le_div_of_nonneg_right (by linarith [hu.2]) hh0.le) (le_max_right _ _)
    have hd_cont : ContinuousOn sincSqDeriv (Set.Icc a b) := by
      unfold sincSqDeriv
      have ha_pos : 0 < a := lt_of_lt_of_le (by positivity) ha
      have hne : ∀ u ∈ Set.Icc a b, u ≠ 0 := fun u hu => (lt_of_lt_of_le ha_pos hu.1).ne'
      refine (continuousOn_const.mul (Real.continuous_sin.continuousOn.div continuousOn_id hne)).mul ?_
      refine ((continuousOn_id.mul Real.continuous_cos.continuousOn).sub
        Real.continuous_sin.continuousOn).div (continuousOn_id.pow 2) ?_
      intro u hu
      exact pow_ne_zero 2 (hne u hu)
    exact hR_comp.mul hd_cont.abs
  have hg_nonneg : ∀ {u : ℝ}, 7 * h ≤ u → 0 ≤ g u := by
    intro u hu
    have hge : Real.exp 1 ≤ 2 * u / h := by
      have h1 : 14 ≤ 2 * u / h := by
        rw [le_div_iff₀ hh0]; linarith
      exact le_trans he_lt_14.le h1
    exact mul_nonneg (hRtrud_nonneg hge) (abs_nonneg _)
  -- Paso 3: extender el límite superior a K * π con K = max 1 ⌈Th / (2π)⌉
  set K : ℕ := max 1 (Nat.ceil (T * h / (2 * Real.pi)))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hTh_le_Kpi : T * h / 2 ≤ (K : ℝ) * Real.pi := by
    have h1 : T * h / (2 * Real.pi) ≤ (Nat.ceil (T * h / (2 * Real.pi)) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (T * h / (2 * Real.pi)) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast le_max_right 1 (Nat.ceil (T * h / (2 * Real.pi)))
    have h3 : T * h / (2 * Real.pi) ≤ (K : ℝ) := le_trans h1 h2
    have hpi : 0 < Real.pi := Real.pi_pos
    have h4 : T * h / (2 * Real.pi) * Real.pi = T * h / 2 := by field_simp
    nlinarith
  have h7h_le_Th : 7 * h ≤ T * h / 2 := by nlinarith
  have h7h_lt_pi3 : 7 * h < Real.pi / 3 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have hpi_le_Kpi : Real.pi ≤ (K : ℝ) * Real.pi := by
    have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    nlinarith [Real.pi_pos]
  have hextend :
      (∫ u in (7 * h)..(T * h / 2), g u) ≤ ∫ u in (7 * h)..((K : ℝ) * Real.pi), g u := by
    have hint1 : IntervalIntegrable g MeasureTheory.volume (7 * h) (T * h / 2) :=
      (hg_cont le_rfl).intervalIntegrable_of_Icc h7h_le_Th
    have hint2 : IntervalIntegrable g MeasureTheory.volume (T * h / 2) ((K : ℝ) * Real.pi) :=
      (hg_cont h7h_le_Th).intervalIntegrable_of_Icc hTh_le_Kpi
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    have hnn : 0 ≤ ∫ u in (T * h / 2)..((K : ℝ) * Real.pi), g u :=
      intervalIntegral.integral_nonneg hTh_le_Kpi (fun u hu => hg_nonneg (le_trans h7h_le_Th hu.1))
    linarith
  -- Descomposición de Rtrud(2u/h) ≤ A + B * ln u para u ≥ 1
  set L : ℝ := Real.log (2 / h)
  have hL_ge : (4.6 : ℝ) ≤ L := by
    have h100 : (100 : ℝ) < 2 / h := by
      rw [lt_div_iff₀ hh0]; linarith
    have hlog100 : (4.6 : ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have he_ub : Real.exp 1 ≤ (2.71829 : ℝ) := le_trans Real.exp_one_lt_d9.le (by norm_num)
      have hpow : (Real.exp 4.6) ^ 5 = (Real.exp 1) ^ 23 := by
        rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul]; norm_num
      have hle : (Real.exp 4.6) ^ 5 ≤ (100 : ℝ) ^ 5 := by
        rw [hpow]
        calc (Real.exp 1) ^ 23 ≤ (2.71829 : ℝ) ^ 23 := by gcongr
          _ ≤ (100 : ℝ) ^ 5 := by norm_num
      by_contra hcon
      push Not at hcon
      have : (100 : ℝ) ^ 5 < (Real.exp 4.6) ^ 5 := by gcongr
      linarith
    exact le_trans hlog100 (Real.log_le_log (by norm_num) h100.le)
  set A : ℝ := 0.112 * L + 0.278 * Real.log L + 2.51
  set B : ℝ := 0.112 + 0.278 / 4.6
  have hRtrud_linear : ∀ {u : ℝ}, 1 ≤ u → Rtrud (2 * u / h) ≤ A + B * Real.log u := by
    intro u hu
    have hu_pos : 0 < u := by linarith
    have h2h_pos : 0 < 2 / h := by positivity
    have harg : 2 * u / h = (2 / h) * u := by ring
    have hlog_eq : Real.log (2 * u / h) = L + Real.log u := by
      rw [harg, Real.log_mul h2h_pos.ne' hu_pos.ne']
    have hc_nn : 0 ≤ Real.log u := Real.log_nonneg hu
    have hL_pos : 0 < L := by linarith
    have hloglog : Real.log (L + Real.log u) ≤ Real.log L + Real.log u / 4.6 := by
      have hfac : L + Real.log u = L * (1 + Real.log u / L) := by field_simp
      have h1pos : 0 < 1 + Real.log u / L := by positivity
      rw [hfac, Real.log_mul hL_pos.ne' h1pos.ne']
      have hle1 : Real.log (1 + Real.log u / L) ≤ Real.log u / L := by
        have := Real.log_le_sub_one_of_pos h1pos
        linarith
      have hle2 : Real.log u / L ≤ Real.log u / 4.6 :=
        div_le_div_of_nonneg_left hc_nn (by norm_num) hL_ge
      linarith
    dsimp [Rtrud, A, B]
    rw [hlog_eq]
    have hmul_eq : 0.278 * (Real.log u / 4.6) = (0.278 / 4.6) * Real.log u := by ring
    linarith only [hloglog, hmul_eq]
  -- Paso 4: integral principal en [7h, π] partida en π/3, π/2, 2π/3, π
  have hmain_part : (∫ u in (7 * h)..Real.pi, g u) ≤ A + B * 0.54 := by
    set a0 : ℝ := 7 * h
    set a1 : ℝ := Real.pi / 3
    set a2 : ℝ := Real.pi / 2
    set a3 : ℝ := 2 * Real.pi / 3
    set a4 : ℝ := Real.pi
    have h01 : a0 ≤ a1 := h7h_lt_pi3.le
    have h12 : a1 ≤ a2 := by dsimp [a1, a2]; linarith [Real.pi_pos]
    have h23 : a2 ≤ a3 := by dsimp [a2, a3]; linarith [Real.pi_pos]
    have h34 : a3 ≤ a4 := by dsimp [a3, a4]; linarith [Real.pi_pos]
    have h0_pos : 0 < a0 := by dsimp [a0]; positivity
    have h1_pos : 0 < a1 := lt_of_lt_of_le h0_pos h01
    have h2_pos : 0 < a2 := lt_of_lt_of_le h1_pos h12
    have h3_pos : 0 < a3 := lt_of_lt_of_le h2_pos h23
    have hint01 : IntervalIntegrable g MeasureTheory.volume a0 a1 :=
      (hg_cont le_rfl).intervalIntegrable_of_Icc h01
    have hint12 : IntervalIntegrable g MeasureTheory.volume a1 a2 :=
      (hg_cont h01).intervalIntegrable_of_Icc h12
    have hint23 : IntervalIntegrable g MeasureTheory.volume a2 a3 :=
      (hg_cont (le_trans h01 h12)).intervalIntegrable_of_Icc h23
    have hint34 : IntervalIntegrable g MeasureTheory.volume a3 a4 :=
      (hg_cont (le_trans (le_trans h01 h12) h23)).intervalIntegrable_of_Icc h34
    have hsplit_main : (∫ u in a0..a4, g u) =
        (∫ u in a0..a1, g u) + (∫ u in a1..a2, g u) + (∫ u in a2..a3, g u) + (∫ u in a3..a4, g u) := by
      have h02 := intervalIntegral.integral_add_adjacent_intervals hint01 hint12
      have h03 := intervalIntegral.integral_add_adjacent_intervals (hint01.trans hint12) hint23
      have h04 := intervalIntegral.integral_add_adjacent_intervals ((hint01.trans hint12).trans hint23) hint34
      linarith
    have hseg : ∀ {x y : ℝ}, a0 ≤ x → x ≤ y → y ≤ Real.pi →
        (∫ u in x..y, g u) ≤ Rtrud (2 * y / h) * (sincSq x - sincSq y) := by
      intro x y hax hxy hypi
      have hx_pos : 0 < x := lt_of_lt_of_le h0_pos hax
      have hd_cont : ContinuousOn (fun u => |sincSqDeriv u|) (Set.Icc x y) := by
        have h1 : ContinuousOn sincSqDeriv (Set.Icc x y) := by
          unfold sincSqDeriv
          have hne : ∀ u ∈ Set.Icc x y, u ≠ 0 := fun u hu => (lt_of_lt_of_le hx_pos hu.1).ne'
          refine (continuousOn_const.mul (Real.continuous_sin.continuousOn.div continuousOn_id hne)).mul ?_
          refine ((continuousOn_id.mul Real.continuous_cos.continuousOn).sub
            Real.continuous_sin.continuousOn).div (continuousOn_id.pow 2) ?_
          intro u hu
          exact pow_ne_zero 2 (hne u hu)
        exact h1.abs
      have hle : (∫ u in x..y, g u) ≤ ∫ u in x..y, Rtrud (2 * y / h) * |sincSqDeriv u| := by
        apply intervalIntegral.integral_mono_on hxy
          ((hg_cont hax).intervalIntegrable_of_Icc hxy)
          ((continuousOn_const.mul hd_cont).intervalIntegrable_of_Icc hxy)
        intro u hu
        dsimp [g]
        have hu_ge : Real.exp 1 ≤ 2 * u / h := by
          have h14 : 14 ≤ 2 * u / h := by rw [le_div_iff₀ hh0]; dsimp [a0] at hax; linarith [hu.1]
          exact le_trans he_lt_14.le h14
        have harg_le : 2 * u / h ≤ 2 * y / h := div_le_div_of_nonneg_right (by linarith [hu.2]) hh0.le
        exact mul_le_mul_of_nonneg_right (hRtrud_mono hu_ge harg_le) (abs_nonneg _)
      rw [intervalIntegral.integral_const_mul, integral_abs_sincSqDeriv_on_zero_pi hx_pos hxy hypi] at hle
      exact hle
    have hI01 := hseg le_rfl h01 (le_trans h12 (le_trans h23 h34))
    have hI12 := hseg h01 h12 (le_trans h23 h34)
    have hI23 := hseg (le_trans h01 h12) h23 h34
    have hI34 := hseg (le_trans (le_trans h01 h12) h23) h34 le_rfl
    -- Valores exactos de sincSq en a1, a2, a3, a4 y cota sincSq a0 ≤ 1
    have hs0_le : sincSq a0 ≤ 1 := by
      unfold sincSq
      have h1 : |Real.sin a0| ≤ |a0| := Real.abs_sin_le_abs
      rw [abs_of_pos h0_pos] at h1
      have h2 : |Real.sin a0 / a0| ≤ 1 := by
        rw [abs_div, abs_of_pos h0_pos, div_le_one h0_pos]; exact h1
      have h3 : (Real.sin a0 / a0) ^ 2 = |Real.sin a0 / a0| ^ 2 := (sq_abs _).symm
      rw [h3]; nlinarith [abs_nonneg (Real.sin a0 / a0)]
    have hs1_eq : sincSq a1 = 27 / (4 * Real.pi ^ 2) := by
      unfold sincSq; dsimp [a1]; rw [Real.sin_pi_div_three]; field_simp
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
    have hs2_eq : sincSq a2 = 4 / Real.pi ^ 2 := by
      unfold sincSq; dsimp [a2]; rw [Real.sin_pi_div_two]; field_simp; ring
    have hs3_eq : sincSq a3 = 27 / (16 * Real.pi ^ 2) := by
      unfold sincSq; dsimp [a3]
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
          Real.sin_pi_div_three]
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
    have hs4_eq : sincSq a4 = 0 := by
      unfold sincSq; dsimp [a4]; rw [Real.sin_pi]; simp
    have hpi_lb : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
    have hpi_ub : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
    have hpi_sq_lb : (3.1415 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
    have hpi_sq_ub : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 := by nlinarith
    set s1 : ℝ := sincSq a1
    set s2 : ℝ := sincSq a2
    set s3 : ℝ := sincSq a3
    have hs1_ub : s1 ≤ 0.68396 := by
      rw [hs1_eq]
      calc 27 / (4 * Real.pi ^ 2) ≤ 27 / (4 * 3.1415 ^ 2) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ ≤ 0.68396 := by norm_num
    have hs1_lb : 0.68389 ≤ s1 := by
      rw [hs1_eq]
      calc (0.68389 : ℝ) ≤ 27 / (4 * 3.1416 ^ 2) := by norm_num
        _ ≤ 27 / (4 * Real.pi ^ 2) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have hs2_ub : s2 ≤ 0.40531 := by
      rw [hs2_eq]
      calc 4 / Real.pi ^ 2 ≤ 4 / 3.1415 ^ 2 :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hpi_sq_lb.le
        _ ≤ 0.40531 := by norm_num
    have hs2_lb : 0.40527 ≤ s2 := by
      rw [hs2_eq]
      calc (0.40527 : ℝ) ≤ 4 / 3.1416 ^ 2 := by norm_num
        _ ≤ 4 / Real.pi ^ 2 :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hpi_sq_ub.le
    have hs3_ub : s3 ≤ 0.17099 := by
      rw [hs3_eq]
      calc 27 / (16 * Real.pi ^ 2) ≤ 27 / (16 * 3.1415 ^ 2) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ ≤ 0.17099 := by norm_num
    have hs3_lb : 0.17097 ≤ s3 := by
      rw [hs3_eq]
      calc (0.17097 : ℝ) ≤ 27 / (16 * 3.1416 ^ 2) := by norm_num
        _ ≤ 27 / (16 * Real.pi ^ 2) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    -- Cotas elementales de ln(a1), ln(a2), ln(a3), ln(a4)
    have he_lb : (2.71828 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
    have hlog_pow : ∀ (x a : ℝ) (p q : ℕ), 0 < x → 0 < q → a * (q : ℝ) = (p : ℝ) →
        x ^ q ≤ (2.71828 : ℝ) ^ p → Real.log x ≤ a := by
      intro x a p q hx hq ha hpow
      rw [Real.log_le_iff_le_exp hx]
      have h1 : (Real.exp a) ^ q = (Real.exp 1) ^ p := by
        rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul, mul_one, mul_comm, ha]
      have h2 : x ^ q ≤ (Real.exp a) ^ q := by
        rw [h1]; exact le_trans hpow (by gcongr)
      by_contra hcon; push Not at hcon
      have : (Real.exp a) ^ q < x ^ q := by gcongr
      linarith
    have hlog_a1 : Real.log a1 ≤ 0.048 := by
      have h1 := Real.log_le_sub_one_of_pos h1_pos
      dsimp [a1] at h1 ⊢; linarith
    have hlog_a2 : Real.log a2 ≤ 0.5 := by
      have ha2_le : a2 ≤ 3.1416 / 2 := by dsimp [a2]; linarith
      exact le_trans (Real.log_le_log h2_pos ha2_le)
        (hlog_pow _ 0.5 1 2 (by norm_num) (by omega) (by norm_num) (by norm_num))
    have hlog_a3 : Real.log a3 ≤ 0.75 := by
      have ha3_le : a3 ≤ 2 * 3.1416 / 3 := by dsimp [a3]; linarith
      exact le_trans (Real.log_le_log h3_pos ha3_le)
        (hlog_pow _ 0.75 3 4 (by norm_num) (by omega) (by norm_num) (by norm_num))
    have hlog_a4 : Real.log a4 ≤ 1.2 := by
      exact le_trans (Real.log_le_log Real.pi_pos hpi_ub.le)
        (hlog_pow _ 1.2 6 5 (by norm_num) (by omega) (by norm_num) (by norm_num))
    have ha1_ge1 : 1 ≤ a1 := by dsimp [a1]; linarith
    have ha2_ge1 : 1 ≤ a2 := le_trans ha1_ge1 h12
    have ha3_ge1 : 1 ≤ a3 := le_trans ha2_ge1 h23
    have ha4_ge1 : 1 ≤ a4 := le_trans ha3_ge1 h34
    have hB_nn : 0 ≤ B := by dsimp [B]; positivity
    have hR1 : Rtrud (2 * a1 / h) ≤ A + B * 0.048 :=
      le_trans (hRtrud_linear ha1_ge1) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog_a1 hB_nn))
    have hR2 : Rtrud (2 * a2 / h) ≤ A + B * 0.5 :=
      le_trans (hRtrud_linear ha2_ge1) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog_a2 hB_nn))
    have hR3 : Rtrud (2 * a3 / h) ≤ A + B * 0.75 :=
      le_trans (hRtrud_linear ha3_ge1) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog_a3 hB_nn))
    have hR4 : Rtrud (2 * a4 / h) ≤ A + B * 1.2 :=
      le_trans (hRtrud_linear ha4_ge1) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog_a4 hB_nn))
    have hR1_nn : 0 ≤ Rtrud (2 * a1 / h) := by
      apply hRtrud_nonneg
      have h14 : 14 ≤ 2 * a1 / h := by rw [le_div_iff₀ hh0]; dsimp [a0] at h01; linarith
      exact le_trans he_lt_14.le h14
    have hI01' : (∫ u in a0..a1, g u) ≤ (A + B * 0.048) * (1 - s1) := by
      have h1 : Rtrud (2 * a1 / h) * (sincSq a0 - s1) ≤ Rtrud (2 * a1 / h) * (1 - s1) :=
        mul_le_mul_of_nonneg_left (by linarith only [hs0_le]) hR1_nn
      have h2 : Rtrud (2 * a1 / h) * (1 - s1) ≤ (A + B * 0.048) * (1 - s1) :=
        mul_le_mul_of_nonneg_right hR1 (by linarith only [hs1_ub])
      exact le_trans hI01 (le_trans h1 h2)
    have hI12' : (∫ u in a1..a2, g u) ≤ (A + B * 0.5) * (s1 - s2) :=
      le_trans hI12 (mul_le_mul_of_nonneg_right hR2 (by linarith only [hs1_lb, hs2_ub]))
    have hI23' : (∫ u in a2..a3, g u) ≤ (A + B * 0.75) * (s2 - s3) :=
      le_trans hI23 (mul_le_mul_of_nonneg_right hR3 (by linarith only [hs2_lb, hs3_ub]))
    have hI34' : (∫ u in a3..a4, g u) ≤ (A + B * 1.2) * s3 := by
      rw [hs4_eq, sub_zero] at hI34
      exact le_trans hI34 (mul_le_mul_of_nonneg_right hR4 (by linarith only [hs3_lb]))
    have hcomb : (A + B * 0.048) * (1 - s1) + (A + B * 0.5) * (s1 - s2) +
        (A + B * 0.75) * (s2 - s3) + (A + B * 1.2) * s3 =
        A + B * (0.048 + 0.452 * s1 + 0.25 * s2 + 0.45 * s3) := by ring
    have hc_main : 0.048 + 0.452 * s1 + 0.25 * s2 + 0.45 * s3 ≤ 0.54 := by
      linarith only [hs1_ub, hs2_ub, hs3_ub]
    have hB_mul : B * (0.048 + 0.452 * s1 + 0.25 * s2 + 0.45 * s3) ≤ B * 0.54 :=
      mul_le_mul_of_nonneg_left hc_main hB_nn
    linarith only [hsplit_main, hI01', hI12', hI23', hI34', hcomb, hB_mul]
  -- Paso 5: cola en [π, Kπ] por períodos [kπ, (k+1)π]
  have htail_part : (∫ u in Real.pi..((K : ℝ) * Real.pi), g u) ≤ A * 0.2126 + B * 0.52 := by
    have hsum_eq : ∀ M : ℕ, 1 ≤ M →
        (∫ u in Real.pi..((M : ℝ) * Real.pi), g u) =
          ∑ k ∈ Finset.Ico 1 M, ∫ u in (k : ℝ) * Real.pi..((k + 1 : ℕ) : ℝ) * Real.pi, g u := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        rw [Finset.sum_Ico_succ_top hm, ← ih]
        have h7_le_pi : 7 * h ≤ Real.pi := by linarith [Real.pi_pos]
        have hpi_le_mpi : Real.pi ≤ (m : ℝ) * Real.pi := by
          have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          nlinarith [Real.pi_pos]
        have hmpi_le_succ : (m : ℝ) * Real.pi ≤ ((m + 1 : ℕ) : ℝ) * Real.pi := by
          push_cast; linarith [Real.pi_pos]
        have hint1 : IntervalIntegrable g MeasureTheory.volume Real.pi ((m : ℝ) * Real.pi) :=
          (hg_cont h7_le_pi).intervalIntegrable_of_Icc hpi_le_mpi
        have hint2 : IntervalIntegrable g MeasureTheory.volume ((m : ℝ) * Real.pi) (((m + 1 : ℕ) : ℝ) * Real.pi) :=
          (hg_cont (le_trans h7_le_pi hpi_le_mpi)).intervalIntegrable_of_Icc hmpi_le_succ
        exact (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
    rw [hsum_eq K hK1]
    have hper : ∀ k ∈ Finset.Ico 1 K,
        (∫ u in (k : ℝ) * Real.pi..((k + 1 : ℕ) : ℝ) * Real.pi, g u) ≤
          A * (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) +
          B * ((2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log (((k + 1 : ℕ) : ℝ) * Real.pi)) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      set ka : ℝ := (k : ℝ) * Real.pi
      set kb : ℝ := ((k + 1 : ℕ) : ℝ) * Real.pi
      have h7_le_ka : 7 * h ≤ ka := by
        have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        dsimp [ka]; nlinarith [Real.pi_pos]
      have hka_pos : 0 < ka := lt_of_lt_of_le (by positivity) h7_le_ka
      have hkab : ka ≤ kb := by dsimp [ka, kb]; push_cast; linarith [Real.pi_pos]
      have hd_cont : ContinuousOn (fun u => |sincSqDeriv u|) (Set.Icc ka kb) := by
        have h1 : ContinuousOn sincSqDeriv (Set.Icc ka kb) := by
          unfold sincSqDeriv
          have hne : ∀ u ∈ Set.Icc ka kb, u ≠ 0 := fun u hu => (lt_of_lt_of_le hka_pos hu.1).ne'
          refine (continuousOn_const.mul (Real.continuous_sin.continuousOn.div continuousOn_id hne)).mul ?_
          refine ((continuousOn_id.mul Real.continuous_cos.continuousOn).sub
            Real.continuous_sin.continuousOn).div (continuousOn_id.pow 2) ?_
          intro u hu
          exact pow_ne_zero 2 (hne u hu)
        exact h1.abs
      have h1 : (∫ u in ka..kb, g u) ≤ Rtrud (2 * kb / h) * ∫ u in ka..kb, |sincSqDeriv u| := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_mono_on hkab
          ((hg_cont h7_le_ka).intervalIntegrable_of_Icc hkab)
          ((continuousOn_const.mul hd_cont).intervalIntegrable_of_Icc hkab)
        intro u hu
        dsimp [g]
        have hu_ge : Real.exp 1 ≤ 2 * u / h := by
          have h14 : 14 ≤ 2 * u / h := by rw [le_div_iff₀ hh0]; linarith [h7_le_ka, hu.1]
          exact le_trans he_lt_14.le h14
        have harg_le : 2 * u / h ≤ 2 * kb / h := div_le_div_of_nonneg_right (by linarith [hu.2]) hh0.le
        exact mul_le_mul_of_nonneg_right (hRtrud_mono hu_ge harg_le) (abs_nonneg _)
      have hR_nn : 0 ≤ Rtrud (2 * kb / h) := by
        apply hRtrud_nonneg
        have h14 : 14 ≤ 2 * kb / h := by rw [le_div_iff₀ hh0]; linarith [h7_le_ka, hkab]
        exact le_trans he_lt_14.le h14
      have h2 : Rtrud (2 * kb / h) * (∫ u in ka..kb, |sincSqDeriv u|) ≤
          Rtrud (2 * kb / h) * (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) :=
        mul_le_mul_of_nonneg_left (sincSq_variation_on_period hk1) hR_nn
      have hkb_ge1 : 1 ≤ kb := by
        dsimp [kb]
        have hk2 : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
        nlinarith [Real.pi_gt_three]
      have h3 : Rtrud (2 * kb / h) * (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) ≤
          (A + B * Real.log kb) * (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) :=
        mul_le_mul_of_nonneg_right (hRtrud_linear hkb_ge1) (by positivity)
      calc (∫ u in ka..kb, g u)
          ≤ (A + B * Real.log kb) * (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) :=
            le_trans h1 (le_trans h2 h3)
        _ = A * (2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) +
            B * ((2 / (1 + (((k : ℝ) + 3 / 8) * Real.pi) ^ 2)) * Real.log kb) := by ring
    have hsum_le := Finset.sum_le_sum hper
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_le
    have hA_nn : 0 ≤ A := by
      dsimp [A]
      have hlogL_nn : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
      linarith
    have hB_nn : 0 ≤ B := by dsimp [B]; positivity
    have hS0 := mul_le_mul_of_nonneg_left (sum_period_S0_le K) hA_nn
    have hS1 := mul_le_mul_of_nonneg_left (sum_period_S1_le K) hB_nn
    linarith
  -- Paso 6: combinar [7h, π] + [π, Kπ] y linealizar ln L ≤ 1.08 + L/8
  have hfull : (∫ u in (7 * h)..((K : ℝ) * Real.pi), g u) ≤ A * 1.2126 + B * 1.06 := by
    have h7_le_pi : 7 * h ≤ Real.pi := by linarith [Real.pi_pos]
    have hint1 : IntervalIntegrable g MeasureTheory.volume (7 * h) Real.pi :=
      (hg_cont le_rfl).intervalIntegrable_of_Icc h7_le_pi
    have hint2 : IntervalIntegrable g MeasureTheory.volume Real.pi ((K : ℝ) * Real.pi) :=
      (hg_cont h7_le_pi).intervalIntegrable_of_Icc hpi_le_Kpi
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    linarith
  have hlogL_ub : Real.log L ≤ 1.08 + L / 8 := by
    have hL_pos : 0 < L := by linarith
    have h8 : Real.log 8 ≤ 2.08 := by
      have h1 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
      rw [h1]
      linarith [Real.log_two_lt_d9]
    have hsplit : Real.log L = Real.log (L / 8) + Real.log 8 := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      congr 1; ring
    have hsub : Real.log (L / 8) ≤ L / 8 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hA_ub : A ≤ 0.112 * L + 0.278 * (1.08 + L / 8) + 2.51 := by
    dsimp [A]; linarith
  have hcomb : -2 * (∫ t in (14 : ℝ)..T, ((zeroCount t : ℝ) - rvmMainTerm t) * f' t) ≤
      2 * (A * 1.2126 + B * 1.06) := by
    have hI : -(∫ t in (14 : ℝ)..T, ((zeroCount t : ℝ) - rvmMainTerm t) * f' t) ≤
        A * 1.2126 + B * 1.06 := by
      calc -(∫ t in (14 : ℝ)..T, ((zeroCount t : ℝ) - rvmMainTerm t) * f' t)
          ≤ ∫ t in (14 : ℝ)..T, Rtrud t * |f' t| := hstep1
        _ = ∫ u in (7 * h)..(T * h / 2), g u := hsub_var
        _ ≤ ∫ u in (7 * h)..((K : ℝ) * Real.pi), g u := hextend
        _ ≤ A * 1.2126 + B * 1.06 := hfull
    linarith
  dsimp [B] at hcomb
  linarith

/-- Cota numérica por integración de Stieltjes de `sinc²(γh/2)` contra `N(T)`,
    demostrada sin `sorry` a partir de `abel_summation_zeros_decomp` y las dos integrales de `sinc²`. -/
lemma pos_zero_sum_sinc_sq_le_of_rvm {h : ℝ} (hh0 : 0 < h) (hh2 : h < 0.02)
    (hRvM : zeroCount 14 = 0 ∧
      ∀ T : ℝ, Real.exp 1 ≤ T →
        |(zeroCount T : ℝ) - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
          0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.51) :
    2 * (∑' ρ : {ρ : ℂ // IsNontrivialZero ρ ∧ 0 < ρ.im}, sincSq (ρ.1.im * h / 2))
      ≤ (1 / h) * Real.log (1 / (Real.pi * h))
          + (0.36 * Real.log (2 / h) + 7.19) := by
  set Pos := {ρ : ℂ // IsNontrivialZero ρ ∧ 0 < ρ.im}
  set B := (1 / h) * Real.log (1 / (Real.pi * h)) + (0.36 * Real.log (2 / h) + 7.19)
  have hsummable : Summable (fun ρ : Pos => sincSq (ρ.1.im * h / 2)) :=
    pos_zero_sum_sinc_sq_summable hh0 hRvM
  suffices htsum : ∑' ρ : Pos, sincSq (ρ.1.im * h / 2) ≤ B / 2 by linarith
  refine hsummable.tsum_le_of_sum_le ?_
  intro s
  apply le_of_forall_pos_le_add
  intro ε hε
  -- Elegimos T ≥ max(14, max_{ρ ∈ s} ρ.im, 24 / (h^2 * ε))
  let M : ℝ := s.fold max 14 (fun ρ => ρ.1.im)
  have h14_le_M : (14 : ℝ) ≤ M := by
    have : ∀ (t : Finset Pos), (14 : ℝ) ≤ t.fold max 14 (fun ρ => ρ.1.im) := by
      intro t
      induction t using Finset.cons_induction with
      | empty => simp
      | cons a t' _ ih =>
        rw [Finset.fold_cons]
        exact le_trans ih (le_max_right _ _)
    exact this s
  have hmem_le_M : ∀ ρ ∈ s, ρ.1.im ≤ M := by
    intro ρ hρ
    have : ∀ (t : Finset Pos), ρ ∈ t → ρ.1.im ≤ t.fold max 14 (fun x => x.1.im) := by
      intro t ht
      induction t using Finset.cons_induction with
      | empty => simp at ht
      | cons a t' _ ih =>
        rw [Finset.fold_cons]
        rw [Finset.mem_cons] at ht
        rcases ht with rfl | ht'
        · exact le_max_left _ _
        · exact le_trans (ih ht') (le_max_right _ _)
    exact this s hρ
  set T : ℝ := max M (24 / (h ^ 2 * ε))
  have h14_le_T : (14 : ℝ) ≤ T := le_trans h14_le_M (le_max_left _ _)
  have hT_pos : 0 < T := by linarith
  have hT_bound : 24 / (h ^ 2 * ε) ≤ T := le_max_right _ _
  -- La suma sobre s está acotada por la suma sobre nontrivialZerosUpTo T
  have hs_le_A :
      ∑ ρ ∈ s, sincSq (ρ.1.im * h / 2) ≤
        ∑ z ∈ (nontrivialZerosUpTo_finite T).toFinset, sincSq (z.im * h / 2) := by
    have himg : s.image Subtype.val ⊆ (nontrivialZerosUpTo_finite T).toFinset := by
      intro z hz
      rw [Finset.mem_image] at hz
      rcases hz with ⟨ρ, hρ, rfl⟩
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2.1, ρ.2.2, le_trans (hmem_le_M ρ hρ) (le_max_left _ _)⟩
    rw [← Finset.sum_image (f := fun z : ℂ => sincSq (z.im * h / 2))
      (fun a _ b _ hab => Subtype.ext hab)]
    exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => sincSq_nonneg _)
  -- Aplicamos abel_summation_zeros_decomp a f(t) = sincSq (t * h / 2)
  have hdecomp := abel_summation_zeros_decomp h14_le_T hRvM.1
    (f := fun t => sincSq (t * h / 2))
    (f' := fun t => (h / 2) * sincSqDeriv (t * h / 2))
    (fun t ht => sincSq_scaled_hasDerivAt hh0 (by linarith [ht.1]))
    (sincSq_scaled_deriv_continuousOn hh0)
  -- 1. Término en t = 14: M(14) * sincSq(7h) ≤ 0
  have hterm14 : rvmMainTerm 14 * sincSq (14 * h / 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg rvmMainTerm_14_neg.le (sincSq_nonneg _)
  -- 2. Término de frontera en T: R(T) * sincSq(Th/2) ≤ ε
  have htermT : ((zeroCount T : ℝ) - rvmMainTerm T) * sincSq (T * h / 2) ≤ ε := by
    have heT : Real.exp 1 ≤ T := by linarith [Real.exp_one_lt_d9]
    have hR := hRvM.2 T heT
    have hlogT_ge1 : (1 : ℝ) ≤ Real.log T := by
      rw [Real.le_log_iff_exp_le hT_pos]; exact heT
    have hR_le : |(zeroCount T : ℝ) - rvmMainTerm T| ≤ 3 * T := by
      have hll : Real.log (Real.log T) ≤ Real.log T := by
        have := Real.log_le_sub_one_of_pos (show 0 < Real.log T by linarith)
        linarith
      have hlogT_le : Real.log T ≤ T := by
        have := Real.log_le_sub_one_of_pos hT_pos
        linarith
      change |(zeroCount T : ℝ) - rvmMainTerm T| ≤ _ at hR
      linarith
    have hsinc_le : sincSq (T * h / 2) ≤ 4 / (h ^ 2 * T ^ 2) := by
      have hu : T * h / 2 ≠ 0 := by positivity
      calc sincSq (T * h / 2) ≤ 1 / (T * h / 2) ^ 2 := sincSq_le_inv_sq hu
        _ = 4 / (h ^ 2 * T ^ 2) := by field_simp; ring
    have hprod_le :
        ((zeroCount T : ℝ) - rvmMainTerm T) * sincSq (T * h / 2) ≤ 12 / (h ^ 2 * T) := by
      calc ((zeroCount T : ℝ) - rvmMainTerm T) * sincSq (T * h / 2)
          ≤ |(zeroCount T : ℝ) - rvmMainTerm T| * sincSq (T * h / 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (sincSq_nonneg _)
        _ ≤ (3 * T) * (4 / (h ^ 2 * T ^ 2)) :=
            mul_le_mul hR_le hsinc_le (sincSq_nonneg _) (by positivity)
        _ = 12 / (h ^ 2 * T) := by field_simp; ring
    have h12_le : 12 / (h ^ 2 * T) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      have h24 : 24 ≤ h ^ 2 * ε * T := by
        rwa [div_le_iff₀ (by positivity), mul_comm] at hT_bound
      nlinarith
    exact le_trans hprod_le h12_le
  -- 3. Integral principal e integral de error
  have hmain := sincSq_main_integral_bound hh0 hh2 h14_le_T
  have herr := sincSq_err_integral_bound hh0 hh2 h14_le_T (fun t ht => hRvM.2 t ht)
  dsimp [B]
  linarith

lemma pos_zero_sum_sinc_sq_bound_of_rvm {h : ℝ} (hh0 : 0 < h) (hh2 : h < 0.02)
    (hRvM : zeroCount 14 = 0 ∧
      ∀ T : ℝ, Real.exp 1 ≤ T →
        |(zeroCount T : ℝ) - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
          0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.51) :
    Summable (fun ρ : {ρ : ℂ // IsNontrivialZero ρ ∧ 0 < ρ.im} => sincSq (ρ.1.im * h / 2)) ∧
    2 * (∑' ρ : {ρ : ℂ // IsNontrivialZero ρ ∧ 0 < ρ.im}, sincSq (ρ.1.im * h / 2))
      ≤ (1 / h) * Real.log (1 / (Real.pi * h))
          + (0.36 * Real.log (2 / h) + 7.19) :=
  ⟨pos_zero_sum_sinc_sq_summable hh0 hRvM, pos_zero_sum_sinc_sq_le_of_rvm hh0 hh2 hRvM⟩

lemma halfWidth_lt_002 {x : ℝ} (hx : 10^5 ≤ x) :
    let Δ := Real.sqrt x * Real.log x
    0 < halfWidth x Δ ∧ halfWidth x Δ < 0.02 := by
  intro Δ
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hΔ0 : 0 < Δ := mul_pos hs0 (Real.log_pos (by linarith))
  have hh0 : 0 < halfWidth x Δ := by
    unfold halfWidth
    exact mul_pos (by norm_num) (Real.log_pos (lt_add_of_pos_right 1 (div_pos hΔ0 hx0)))
  refine ⟨hh0, ?_⟩
  have hL_lt : Real.log x < 0.04 * Real.sqrt x := by
    set s := Real.sqrt x
    have hs316 : 316 ≤ s := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; norm_num; linarith
    have hlogx : Real.log x = 2 * Real.log s := by
      dsimp [s]
      rw [Real.log_sqrt hx0.le]; ring
    have hlog316 : Real.log 316 ≤ 6 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he : (2.71828 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      have : Real.exp 6 = (Real.exp 1) ^ (6 : ℕ) := by
        rw [← Real.exp_natCast_mul]; norm_num
      rw [this]
      calc (316 : ℝ) ≤ (2.71828 : ℝ) ^ (6 : ℕ) := by norm_num
        _ ≤ (Real.exp 1) ^ (6 : ℕ) := by gcongr
    have h1 := Real.log_le_sub_one_of_pos (div_pos hs0 (by norm_num : (0 : ℝ) < 316))
    rw [Real.log_div hs0.ne' (by norm_num)] at h1
    have hdiv : s / 316 = (1 / 316 : ℝ) * s := by ring
    rw [hdiv] at h1
    linarith
  have hΔx : Δ / x < 0.04 := by
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hrew : Δ / x = Real.log x / Real.sqrt x := by
      dsimp [Δ]
      rw [div_eq_div_iff hx0.ne' hs0.ne']
      calc Real.sqrt x * Real.log x * Real.sqrt x
          = (Real.sqrt x * Real.sqrt x) * Real.log x := by ring
        _ = Real.log x * x := by rw [hsq, mul_comm]
    rw [hrew, div_lt_iff₀ hs0]
    linarith
  unfold halfWidth
  have hlog_le : Real.log (1 + Δ / x) ≤ Δ / x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Δ / x by positivity)
    linarith
  linarith

lemma zero_sum_sinc_sq_bound {x : ℝ} (hx : 10^5 ≤ x) :
    let Δ := Real.sqrt x * Real.log x
    let h := halfWidth x Δ
    ∑' ρ : {ρ : ℂ // IsNontrivialZero ρ},
      (Real.sin (ρ.1.im * h / 2) / (ρ.1.im * h / 2)) ^ 2
    ≤ (1 / h) * Real.log (1 / (Real.pi * h))
        + (0.36 * Real.log (2 / h) + 7.19) := by
  intro Δ h
  rcases halfWidth_lt_002 hx with ⟨hh0, hh2⟩
  rcases pos_zero_sum_sinc_sq_bound_of_rvm hh0 hh2 riemann_von_mangoldt_trudgian with ⟨hsum, hbound⟩
  have hsym := tsum_nontrivialZeros_eq_two_mul_pos h hsum
  simpa [sincSq] using hsym.le.trans hbound

/-! ### Ensamblaje de las cotas analíticas (sin sorry) -/

lemma explicit_formula_triKernel_lower_bound
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 10^5 ≤ x) :
    let Δ := Real.sqrt x * Real.log x
    let h := halfWidth x Δ
    Real.sqrt x - (1 / h) * Real.log (1 / (Real.pi * h))
      - (0.36 * Real.log (2 / h) + 7.2)
    ≤ weightedVonMangoldt x Δ := by
  intro Δ h
  have hx0 : 0 < x := by linarith
  have hΔ0 : 0 < Δ := mul_pos (Real.sqrt_pos.mpr hx0) (Real.log_pos (by linarith))
  have hMain := mellinTriWeight_at_one_ge_sqrt hx0 hΔ0
  have hWeil := weil_explicit_formula_triWeight hx
  have hSum := zero_sum_sinc_sq_bound hx
  have hEq :
      (∑' ρ : {ρ : ℂ // IsNontrivialZero ρ}, ‖mellinTriWeight x Δ ρ.1‖) =
      (∑' ρ : {ρ : ℂ // IsNontrivialZero ρ},
        (Real.sin (ρ.1.im * h / 2) / (ρ.1.im * h / 2)) ^ 2) := by
    congr 1
    ext ⟨ρ, hρ⟩
    have hre : ρ.re = 1 / 2 := hRH ρ hρ.1 hρ.2.1 hρ.2.2
    exact norm_mellinTriWeight_on_critical_line hre
  dsimp only at hWeil hSum
  rw [hEq] at hWeil
  linarith

lemma weightedVonMangoldt_le_properPrimePowerSum
    {x Δ : ℝ} (hx : 1 ≤ x) (hΔ : 0 < Δ)
    (hNoPrime : ∀ p : ℕ, Nat.Prime p → ¬ (x < (p : ℝ) ∧ (p : ℝ) ≤ x + Δ)) :
    weightedVonMangoldt x Δ ≤
      (1 / (halfWidth x Δ * Real.sqrt x)) * properPrimePowerSum (Nat.floor (x + Δ)) := by
  unfold weightedVonMangoldt properPrimePowerSum
  have hx0 : 0 < x := by linarith
  have hh : 0 < halfWidth x Δ := by
    unfold halfWidth
    exact mul_pos (by norm_num) (Real.log_pos (lt_add_of_pos_right 1 (div_pos hΔ hx0)))
  have hterm :
      ∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor (x + Δ)),
        (vonMangoldt n) * smoothWeight x Δ (Real.log n)
      ≤ ∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor (x + Δ)),
        (vonMangoldt n) * (1 / (halfWidth x Δ * Real.sqrt x)) := by
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hxn : x < (n : ℝ) := (Nat.floor_lt hx0.le).mp hn.1
    exact mul_le_mul_of_nonneg_left
      (smoothWeight_le_inv_mul_sqrt hx0 hΔ hxn)
      ArithmeticFunction.vonMangoldt_nonneg
  rw [← Finset.sum_mul, mul_comm] at hterm
  have hsub :
      Finset.Ioc (Nat.floor x) (Nat.floor (x + Δ)) ⊆
        (Finset.Icc 1 (Nat.floor (x + Δ))).filter (fun n => ¬ Nat.Prime n) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hxn : x < (n : ℝ) := (Nat.floor_lt hx0.le).mp hn.1
    have hnxΔ : (n : ℝ) ≤ x + Δ := (Nat.le_floor_iff (by linarith)).mp hn.2
    refine ⟨⟨?_, hn.2⟩, fun hp => hNoPrime n hp ⟨hxn, hnxΔ⟩⟩
    have : 1 ≤ Nat.floor x := Nat.le_floor (by exact_mod_cast hx)
    omega
  have hsum_le :
      ∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor (x + Δ)), (vonMangoldt n : ℝ)
      ≤ ∑ n ∈ (Finset.Icc 1 (Nat.floor (x + Δ))).filter (fun n => ¬ Nat.Prime n),
          (vonMangoldt n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  calc weightedVonMangoldt x Δ
      ≤ (1 / (halfWidth x Δ * Real.sqrt x)) *
          ∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor (x + Δ)), (vonMangoldt n : ℝ) := hterm
    _ ≤ (1 / (halfWidth x Δ * Real.sqrt x)) * properPrimePowerSum (Nat.floor (x + Δ)) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)

lemma prime_powers_upper_bound
    {x Δ : ℝ} (hx : 10^5 ≤ x) (hΔ : Δ = Real.sqrt x * Real.log x)
    (hNoPrime : ∀ p : ℕ, Nat.Prime p → ¬ (x < (p : ℝ) ∧ (p : ℝ) ≤ x + Δ)) :
    let h := halfWidth x Δ
    weightedVonMangoldt x Δ ≤ (2 / h) * Real.sqrt (1 + Δ / x) := by
  intro h
  have hx0 : 0 < x := by linarith
  have hΔ0 : 0 < Δ := by
    rw [hΔ]
    exact mul_pos (Real.sqrt_pos.mpr hx0) (Real.log_pos (by linarith))
  have hh : 0 < h := by
    dsimp [h, halfWidth]
    exact mul_pos (by norm_num) (Real.log_pos (lt_add_of_pos_right 1 (div_pos hΔ0 hx0)))
  have h1 := weightedVonMangoldt_le_properPrimePowerSum (by linarith) hΔ0 hNoPrime
  have h2 := properPrimePowerSum_le_two_sqrt (Y := x + Δ) (by linarith)
  have hratio : Real.sqrt (x + Δ) / Real.sqrt x = Real.sqrt (1 + Δ / x) := by
    rw [← Real.sqrt_div (by linarith : 0 ≤ x + Δ), add_div, div_self hx0.ne']
  calc weightedVonMangoldt x Δ
      ≤ (1 / (h * Real.sqrt x)) * properPrimePowerSum (Nat.floor (x + Δ)) := h1
    _ ≤ (1 / (h * Real.sqrt x)) * (2 * Real.sqrt (x + Δ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 / h) * (Real.sqrt (x + Δ) / Real.sqrt x) := by ring
    _ = (2 / h) * Real.sqrt (1 + Δ / x) := by rw [hratio]

/-! ### Desigualdad numérica para x ≥ 10^5 (sin sorry) -/

lemma div_one_add_le_log_one_add {u : ℝ} (hu : 0 < u) :
    u / (1 + u) ≤ Real.log (1 + u) := by
  have h1 : 0 < 1 + u := by linarith
  have hexp : (-u / (1 + u)) + 1 ≤ Real.exp (-u / (1 + u)) :=
    Real.add_one_le_exp _
  have hsimp : (-u / (1 + u)) + 1 = (1 + u)⁻¹ := by
    field_simp; ring
  rw [hsimp] at hexp
  have hlog := Real.log_le_log (inv_pos.mpr h1) hexp
  rw [Real.log_inv, Real.log_exp, neg_div] at hlog
  linarith

lemma exp_half_lower_bound {L : ℝ} (hL : 11.5 ≤ L) :
    314 * (1 + (L / 2 - 5.75) + (L / 2 - 5.75) ^ 2 / 2) ≤ Real.exp (L / 2) := by
  set y := L / 2 - 5.75
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hsplit : Real.exp (L / 2) = Real.exp 5.75 * Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have h575 : (314 : ℝ) ≤ Real.exp 5.75 := by
    have he : (2.71828 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
    have hpow : (2.71828 : ℝ) ^ (23 : ℕ) ≤ (Real.exp 1) ^ (23 : ℕ) := by gcongr
    have h4 : (314 : ℝ) ^ (4 : ℕ) ≤ (Real.exp 5.75) ^ (4 : ℕ) := by
      have h23 : (Real.exp 5.75) ^ (4 : ℕ) = (Real.exp 1) ^ (23 : ℕ) := by
        rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul]; norm_num
      rw [h23]
      exact le_trans (by norm_num) hpow
    by_contra hcon
    push Not at hcon
    have : (Real.exp 5.75) ^ (4 : ℕ) < (314 : ℝ) ^ (4 : ℕ) := by gcongr
    linarith
  have htay : 1 + y + y ^ 2 / 2 ≤ Real.exp y := by
    simpa [Finset.sum_range_succ, Nat.factorial] using Real.sum_le_exp_of_nonneg hy 3
  exact mul_le_mul h575 htay (by positivity) (by positivity)

lemma analytic_margin_pos {x : ℝ} (hx : 10^5 ≤ x) :
    let Δ := Real.sqrt x * Real.log x
    let h := halfWidth x Δ
    (2 / h) * Real.sqrt (1 + Δ / x) <
      Real.sqrt x - (1 / h) * Real.log (1 / (Real.pi * h))
        - (0.36 * Real.log (2 / h) + 7.2) := by
  intro Δ h
  set s := Real.sqrt x
  set L := Real.log x
  set u := L / s
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  have hs_eq : s = Real.exp (L / 2) := by
    dsimp [s, L]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]; ring_nf
  have hΔx : Δ / x = u := by
    dsimp [Δ, u, s, L]
    rw [div_eq_div_iff hx0.ne' hs0.ne']
    calc Real.sqrt x * Real.log x * Real.sqrt x
        = (Real.sqrt x * Real.sqrt x) * Real.log x := by ring
      _ = Real.log x * x := by rw [Real.mul_self_sqrt hx0.le, mul_comm]
  have hL115 : 11.5 ≤ L := by
    rw [Real.le_log_iff_exp_le hx0]
    have he : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h23 : Real.exp 23 < (10^5 : ℝ) ^ 2 := by
      have : Real.exp 23 = (Real.exp 1) ^ (23 : ℕ) := by
        rw [← Real.exp_natCast_mul]; norm_num
      rw [this]
      calc (Real.exp 1) ^ (23 : ℕ) < (2.7183 : ℝ) ^ (23 : ℕ) := by gcongr
        _ < (10^5 : ℝ) ^ 2 := by norm_num
    have hsq : (Real.exp 11.5) ^ 2 < (10^5 : ℝ) ^ 2 := by
      rw [← Real.exp_natCast_mul]
      convert h23 using 2
      norm_num
    nlinarith [Real.exp_pos 11.5]
  have hs_quad : 314 * (1 + (L / 2 - 5.75) + (L / 2 - 5.75) ^ 2 / 2) ≤ s := by
    rw [hs_eq]; exact exp_half_lower_bound hL115
  have hu0 : 0 < u := div_pos (by linarith) hs0
  have hu04 : u < 0.04 := by
    rw [div_lt_iff₀ hs0]; nlinarith
  have hh0 : 0 < h := by
    dsimp [h, halfWidth]; rw [hΔx]
    exact mul_pos (by norm_num) (Real.log_pos (by linarith))
  have h_inv_h : 1 / h ≤ 2 * s / L + 2 := by
    dsimp [h, halfWidth]; rw [hΔx]
    have hlog := div_one_add_le_log_one_add hu0
    have hrec : 1 / ((1 / 2) * Real.log (1 + u)) ≤ 2 * (1 + u) / u := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) (Real.log_pos (by linarith))) hu0]
      have : u ≤ (1 + u) * Real.log (1 + u) := by
        rw [mul_comm]
        exact (div_le_iff₀ (by linarith)).mp hlog
      linarith
    have hEq : 2 * (1 + u) / u = 2 * s / L + 2 := by
      dsimp [u]; field_simp
    linarith
  have h_inv_h' : 1 / h ≤ 2 * (s / L) + 2 := by
    rw [← mul_div_assoc]; exact h_inv_h
  have hsqrt_u : Real.sqrt (1 + u) ≤ 1.02 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hlog_pih : Real.log (1 / (Real.pi * h)) ≤ L / 2 - Real.log L := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h1 : 1 / (Real.pi * h) ≤ s / L := by
      have : 1 / h ≤ 2.08 * (s / L) := by
        have h2s : 2 ≤ 0.08 * (s / L) := by
          have : 25 * L < s := by linarith [div_lt_iff₀ hs0 |>.mp hu04]
          rw [← mul_div_assoc, le_div_iff₀ (by linarith)]; linarith
        linarith
      have hrew : 1 / (Real.pi * h) = Real.pi⁻¹ * (1 / h) := by ring
      rw [hrew]
      calc Real.pi⁻¹ * (1 / h) ≤ (3 : ℝ)⁻¹ * (2.08 * (s / L)) := by gcongr
        _ ≤ s / L := by
            have : 0 < s / L := div_pos hs0 (by linarith)
            nlinarith
    calc Real.log (1 / (Real.pi * h)) ≤ Real.log (s / L) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log s - Real.log L := Real.log_div hs0.ne' (by linarith)
      _ = L / 2 - Real.log L := by rw [hs_eq, Real.log_exp]
  have hlog_2h : Real.log (2 / h) ≤ L / 2 := by
    have h1 : 2 / h ≤ s := by
      have h2s : 2 ≤ 0.08 * (s / L) := by
        have : 25 * L < s := by linarith [div_lt_iff₀ hs0 |>.mp hu04]
        rw [← mul_div_assoc, le_div_iff₀ (by linarith)]; linarith
      have h2eq : 2 / h = 2 * (1 / h) := by ring
      have : 2 / h ≤ 4.16 * (s / L) := by linarith
      have : 4.16 * (s / L) ≤ s := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
      linarith
    calc Real.log (2 / h) ≤ Real.log s := Real.log_le_log (by positivity) h1
      _ = L / 2 := by rw [hs_eq, Real.log_exp]
  have hlogL : 2.44 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have he : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h61 : Real.exp 61 < (11.5 : ℝ) ^ (25 : ℕ) := by
      have : Real.exp 61 = (Real.exp 1) ^ (61 : ℕ) := by
        rw [← Real.exp_natCast_mul]; norm_num
      rw [this]
      calc (Real.exp 1) ^ (61 : ℕ) < (2.7183 : ℝ) ^ (61 : ℕ) := by gcongr
        _ < (11.5 : ℝ) ^ (25 : ℕ) := by norm_num
    have h25 : (Real.exp 2.44) ^ (25 : ℕ) < (11.5 : ℝ) ^ (25 : ℕ) := by
      rw [← Real.exp_natCast_mul]
      convert h61 using 2
      norm_num
    by_contra hcon
    push Not at hcon
    have h115_le : (11.5 : ℝ) ≤ Real.exp 2.44 := by linarith
    have : (11.5 : ℝ) ^ (25 : ℕ) ≤ (Real.exp 2.44) ^ (25 : ℕ) := by gcongr
    linarith
  have hcoef_pos : 0 < L / 2 - Real.log L + 2.04 := by
    have hlog_half := Real.log_le_sub_one_of_pos (show 0 < L / 2 by linarith)
    have hlog2 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [Real.exp_one_gt_d9]
    have hsplitL : Real.log L = Real.log (L / 2) + Real.log 2 := by
      rw [← Real.log_mul (by linarith) (by norm_num)]; ring_nf
    linarith
  have hmain :
      (1 / h) * (Real.log (1 / (Real.pi * h)) + 2 * Real.sqrt (1 + u))
      ≤ (2 * s / L + 2) * (L / 2 - Real.log L + 2.04) := by
    calc (1 / h) * (Real.log (1 / (Real.pi * h)) + 2 * Real.sqrt (1 + u))
        ≤ (1 / h) * (L / 2 - Real.log L + 2.04) := by gcongr; linarith
      _ ≤ (2 * s / L + 2) * (L / 2 - Real.log L + 2.04) :=
          mul_le_mul_of_nonneg_right h_inv_h hcoef_pos.le
  have hfinal : 1.18 * L ^ 2 + 6.40 * L < 0.80 * s := by nlinarith
  have hdiv : 1.18 * L + 6.40 < 0.80 * s / L := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hsimp :
      (2 * s / L + 2) * (L / 2 - Real.log L + 2.04) + (0.36 * (L / 2) + 7.2) < s := by
    have hL0 : L ≠ 0 := by linarith
    have hexpand :
        (2 * s / L + 2) * (L / 2 - Real.log L + 2.04)
        = s - 2 * s * (Real.log L - 2.04) / L + L - 2 * Real.log L + 4.08 := by
      field_simp; ring
    rw [hexpand]
    have h080 : 0.80 * s / L ≤ 2 * s * (Real.log L - 2.04) / L := by
      rw [div_le_div_iff_of_pos_right (by linarith)]; nlinarith
    linarith
  rw [hΔx]
  have hdist :
      (1 / h) * Real.log (1 / (Real.pi * h)) + (2 / h) * Real.sqrt (1 + u)
      = (1 / h) * (Real.log (1 / (Real.pi * h)) + 2 * Real.sqrt (1 + u)) := by ring
  linarith

/-! ### Caso finito 4 ≤ x < 10^5 -/

/-- Todos los primos ≤ 316 (suficientes para certificar primalidad hasta 317² = 100489). -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
   83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
   173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257,
   263, 269, 271, 277, 281, 283, 293, 307, 311, 313]

/-- Test de primalidad estructural (sin `WellFounded.fix`) válido para `n ≤ 100488`. -/
def isFastPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && decide (n ≤ 100488) &&
    smallPrimes.all (fun q => decide (n ≤ q) || decide (n % q ≠ 0))

/-- Comprueba que todo `d ∈ [2, 316]` tiene un divisor en `smallPrimes`. -/
def checkSmallPrimesCover : ℕ → Bool
  | 0 => true
  | d + 1 =>
      (if d + 1 < 2 then true else smallPrimes.any (fun q => decide (q ≤ d + 1) && decide ((d + 1) % q = 0))) &&
      checkSmallPrimesCover d

lemma checkSmallPrimesCover_316 : checkSmallPrimesCover 316 = true := by decide +kernel

lemma smallPrimes_covers {d : ℕ} (hd2 : 2 ≤ d) (hd316 : d ≤ 316) :
    ∃ q ∈ smallPrimes, q ≤ d ∧ q ∣ d := by
  have haux : ∀ m, checkSmallPrimesCover m = true → ∀ k, 2 ≤ k → k ≤ m →
      ∃ q ∈ smallPrimes, q ≤ k ∧ q ∣ k := by
    intro m hm
    induction m with
    | zero => intro k hk2 hk0; omega
    | succ n ih =>
      simp only [checkSmallPrimesCover, Bool.and_eq_true] at hm
      intro k hk2 hkn
      by_cases hEq : k = n + 1
      · subst hEq
        have h1 := hm.1
        have hnotlt : ¬ (n + 1 < 2) := by omega
        simp only [hnotlt, ↓reduceIte, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
        rcases h1 with ⟨q, hqmem, hqle, hqmod⟩
        exact ⟨q, hqmem, hqle, Nat.dvd_of_mod_eq_zero hqmod⟩
      · exact ih hm.2 k hk2 (by omega)
  exact haux 316 checkSmallPrimesCover_316 d hd2 hd316

lemma isFastPrime_sound {n : ℕ} (h : isFastPrime n = true) : Nat.Prime n := by
  simp only [isFastPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  rcases h with ⟨⟨hn2, hnmax⟩, hall⟩
  by_contra hnp
  rcases Nat.exists_dvd_of_not_prime2 hn2 hnp with ⟨a, hadvd, ha2, han⟩
  rcases hadvd with ⟨b, hnab⟩
  have hb2 : 2 ≤ b := by
    by_contra hb
    have hb1 : b = 0 ∨ b = 1 := by omega
    rcases hb1 with rfl | rfl <;> omega
  set d := min a b
  have hd2 : 2 ≤ d := le_min ha2 hb2
  have hd_dvd : d ∣ n := by
    by_cases hle : a ≤ b
    · rw [show d = a from min_eq_left hle]; exact ⟨b, hnab⟩
    · rw [show d = b from min_eq_right (le_of_not_ge hle)]; exact ⟨a, by rw [mul_comm]; exact hnab⟩
  have hd_sq : d * d ≤ n := by
    have : d * d ≤ a * b := Nat.mul_le_mul (min_le_left a b) (min_le_right a b)
    omega
  have hd316 : d ≤ 316 := by nlinarith
  rcases smallPrimes_covers hd2 hd316 with ⟨q, hqmem, hqd, hqdvd⟩
  have hqn : q ∣ n := dvd_trans hqdvd hd_dvd
  have hqlt : q < n := by
    have hdn : d < n := by nlinarith
    omega
  rcases hall q hqmem with hle | hmod
  · omega
  · exact hmod (Nat.mod_eq_zero_of_dvd hqn)

/-- Comprueba de forma decidible que una lista son primos estrictamente crecientes
    con saltos `(q - p)^2 ≤ 2 * p`. -/
def isValidLadder : List ℕ → Bool
  | [] => true
  | [p] => isFastPrime p
  | p :: q :: rest =>
      isFastPrime p && decide (p < q) && decide ((q - p) ^ 2 ≤ 2 * p) &&
        isValidLadder (q :: rest)

/-- Escalera de primos desde 11 hasta 100129 (> 10^5) con `(q - p)^2 ≤ 2 * p`. -/
def primeLadder : List ℕ := [
  11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 53, 61, 71, 79, 89, 101, 113, 127, 139, 151, 167,
  181, 199, 211, 229, 241, 257, 277, 293, 317, 337, 359, 383, 409, 433, 461, 491, 521, 547,
  577, 607, 641, 673, 709, 743, 773, 811, 839, 877, 911, 953, 991, 1033, 1069, 1109, 1153,
  1201, 1249, 1297, 1327, 1373, 1423, 1471, 1523, 1571, 1627, 1669, 1723, 1777, 1831, 1889,
  1949, 2011, 2069, 2131, 2179, 2243, 2309, 2371, 2437, 2503, 2557, 2621, 2693, 2753, 2819,
  2887, 2957, 3023, 3089, 3167, 3229, 3307, 3373, 3449, 3529, 3613, 3697, 3779, 3863, 3947,
  4027, 4111, 4201, 4289, 4373, 4463, 4549, 4643, 4733, 4817, 4909, 5003, 5101, 5197, 5297,
  5399, 5501, 5591, 5693, 5791, 5897, 5987, 6091, 6199, 6301, 6397, 6491, 6599, 6709, 6823,
  6917, 7027, 7129, 7247, 7351, 7459, 7577, 7699, 7823, 7937, 8059, 8179, 8297, 8423, 8543,
  8669, 8783, 8893, 9013, 9137, 9257, 9391, 9521, 9649, 9787, 9923, 10061, 10193, 10333,
  10463, 10607, 10739, 10883, 11027, 11173, 11321, 11471, 11621, 11743, 11887, 12041, 12163,
  12301, 12457, 12613, 12763, 12919, 13063, 13219, 13381, 13537, 13697, 13859, 14011, 14177,
  14341, 14503, 14669, 14831, 14983, 15149, 15319, 15493, 15667, 15823, 15991, 16141, 16319,
  16493, 16673, 16843, 17021, 17203, 17387, 17573, 17749, 17929, 18097, 18287, 18461, 18637,
  18803, 18979, 19163, 19333, 19507, 19699, 19891, 20089, 20287, 20483, 20681, 20879, 21067,
  21269, 21467, 21673, 21881, 22079, 22283, 22483, 22691, 22901, 23099, 23311, 23509, 23719,
  23929, 24137, 24337, 24551, 24767, 24989, 25189, 25411, 25633, 25849, 26053, 26267, 26489,
  26717, 26947, 27179, 27409, 27631, 27851, 28087, 28319, 28549, 28771, 29009, 29243, 29483,
  29723, 29959, 30203, 30431, 30677, 30911, 31159, 31397, 31643, 31891, 32143, 32381, 32633,
  32887, 33119, 33359, 33617, 33871, 34129, 34381, 34631, 34883, 35141, 35401, 35617, 35879,
  36137, 36389, 36653, 36923, 37189, 37447, 37717, 37991, 38261, 38501, 38767, 39043, 39317,
  39581, 39857, 40129, 40387, 40639, 40903, 41189, 41467, 41737, 42023, 42307, 42589, 42863,
  43151, 43441, 43721, 43997, 44293, 44587, 44879, 45161, 45439, 45737, 46027, 46327, 46619,
  46919, 47221, 47527, 47819, 48121, 48413, 48679, 48991, 49297, 49603, 49891, 50177, 50461,
  50777, 51071, 51383, 51691, 52009, 52321, 52639, 52963, 53281, 53597, 53923, 54251, 54577,
  54907, 55229, 55547, 55871, 56197, 56531, 56857, 57193, 57529, 57859, 58199, 58537, 58831,
  59167, 59509, 59833, 60169, 60509, 60821, 61169, 61511, 61861, 62207, 62549, 62897, 63247,
  63601, 63949, 64303, 64661, 65011, 65371, 65731, 66089, 66449, 66809, 67169, 67531, 67891,
  68239, 68597, 68963, 69317, 69677, 70039, 70393, 70753, 71129, 71503, 71881, 72253, 72623,
  72997, 73379, 73757, 74131, 74509, 74891, 75277, 75659, 76039, 76423, 76801, 77191, 77573,
  77951, 78341, 78721, 79111, 79493, 79889, 80287, 80687, 81083, 81463, 81853, 82241, 82633,
  83023, 83423, 83813, 84221, 84631, 85037, 85447, 85853, 86263, 86677, 87083, 87491, 87887,
  88301, 88721, 89137, 89533, 89939, 90359, 90749, 91163, 91583, 92009, 92431, 92857, 93287,
  93703, 94121, 94547, 94961, 95393, 95819, 96233, 96671, 97103, 97523, 97961, 98389, 98809,
  99251, 99689, 100129
]

set_option maxRecDepth 4096 in
lemma primeLadder_valid : isValidLadder primeLadder = true := by decide +kernel

lemma isValidLadder_head_prime {p : ℕ} {l : List ℕ}
    (h : isValidLadder (p :: l) = true) : Nat.Prime p := by
  cases l with
  | nil =>
    exact isFastPrime_sound (by simpa [isValidLadder] using h)
  | cons q rest =>
    simp only [isValidLadder, Bool.and_eq_true, decide_eq_true_eq] at h
    exact isFastPrime_sound h.1.1.1

lemma exists_in_valid_ladder :
    ∀ (l : List ℕ) (p₀ : ℕ) (x : ℝ),
      isValidLadder (p₀ :: l) = true →
      (p₀ : ℝ) ≤ x →
      x < ((p₀ :: l).getLast (List.cons_ne_nil _ _) : ℝ) →
      ∃ p q : ℕ, Nat.Prime q ∧ (p : ℝ) ≤ x ∧ x < (q : ℝ) ∧ p < q ∧ (q - p) ^ 2 ≤ 2 * p
  | [], p₀, x, _, hle, hlt => by
      simp only [List.getLast_singleton] at hlt
      linarith
  | q :: rest, p₀, x, hvalid, hle, hlt => by
      have hv := hvalid
      simp only [isValidLadder, Bool.and_eq_true, decide_eq_true_eq] at hv
      rcases hv with ⟨⟨⟨_, hp₀q⟩, hstep⟩, hrest⟩
      have hq : Nat.Prime q := isValidLadder_head_prime hrest
      by_cases hxq : x < (q : ℝ)
      · exact ⟨p₀, q, hq, hle, hxq, hp₀q, hstep⟩
      · have hle' : (q : ℝ) ≤ x := le_of_not_gt hxq
        have hlt' : x < ((q :: rest).getLast (List.cons_ne_nil _ _) : ℝ) := by
          simpa using hlt
        exact exists_in_valid_ladder rest q x hrest hle' hlt'

lemma log_five_gt_16 : (1.6 : ℝ) < Real.log 5 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have he : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h8 : Real.exp 8 < (5 : ℝ) ^ (5 : ℕ) := by
    have : Real.exp 8 = (Real.exp 1) ^ (8 : ℕ) := by
      rw [← Real.exp_natCast_mul]; norm_num
    rw [this]
    calc (Real.exp 1) ^ (8 : ℕ) < (2.7183 : ℝ) ^ (8 : ℕ) := by gcongr
      _ < (5 : ℝ) ^ (5 : ℕ) := by norm_num
  have h5 : (Real.exp 1.6) ^ (5 : ℕ) < (5 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.exp_natCast_mul]
    convert h8 using 2
    norm_num
  by_contra hcon
  push Not at hcon
  have : (5 : ℝ) ^ (5 : ℕ) ≤ (Real.exp 1.6) ^ (5 : ℕ) := by gcongr
  linarith

lemma sqrt_two_lt_log_five : Real.sqrt 2 < Real.log 5 := by
  have h1 : Real.sqrt 2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith [log_five_gt_16]

lemma exists_prime_small {x : ℝ} (hx4 : 4 ≤ x) (hx5 : x < 10^5) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + Real.sqrt x * Real.log x := by
  have hx0 : 0 < x := by linarith
  by_cases h5 : x < 5
  · refine ⟨5, by decide, h5, ?_⟩
    have hsq : (2 : ℝ) ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
    have hlog : (1 : ℝ) < Real.log x := by
      have hlog4 : (1 : ℝ) < Real.log 4 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        linarith [Real.exp_one_lt_d9]
      exact lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) hx4)
    push_cast; nlinarith
  · push Not at h5
    by_cases h7 : x < 7
    · refine ⟨7, by decide, h7, ?_⟩
      have hsq : (2 : ℝ) ≤ Real.sqrt x := by
        rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
      have hlog : (1.6 : ℝ) < Real.log x :=
        lt_of_lt_of_le log_five_gt_16 (Real.log_le_log (by norm_num) h5)
      push_cast; nlinarith
    · push Not at h7
      by_cases h11 : x < 11
      · refine ⟨11, by decide, h11, ?_⟩
        have hsq : (2.6 : ℝ) ≤ Real.sqrt x := by
          rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
        have hlog : (1.6 : ℝ) < Real.log x :=
          lt_of_lt_of_le log_five_gt_16 (Real.log_le_log (by norm_num) (by linarith))
        push_cast; nlinarith
      · push Not at h11
        have hlast : (primeLadder.getLast (by decide) : ℝ) = 100129 := by
          have : primeLadder.getLast (by decide) = 100129 := by decide +kernel
          exact_mod_cast this
        have hx_last : x < (primeLadder.getLast (by decide) : ℝ) := by
          rw [hlast]; norm_num at hx5 ⊢; linarith
        rcases exists_in_valid_ladder primeLadder.tail 11 x primeLadder_valid h11 hx_last with
          ⟨p, q, hq, hpx, hxq, hpq, hstep⟩
        refine ⟨q, hq, hxq, ?_⟩
        have hdiff_le : ((q : ℝ) - (p : ℝ)) ≤ Real.sqrt 2 * Real.sqrt x := by
          have hsub : (0 : ℝ) ≤ (q : ℝ) - (p : ℝ) := by
            have : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
            linarith
          have hstepR : ((q : ℝ) - (p : ℝ)) ^ 2 ≤ 2 * (p : ℝ) := by
            have hcast : ((q - p : ℕ) : ℝ) ^ 2 ≤ 2 * (p : ℝ) := by exact_mod_cast hstep
            rwa [Nat.cast_sub hpq.le] at hcast
          have hsq_le : ((q : ℝ) - (p : ℝ)) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt x) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hx0.le]
            linarith
          nlinarith [mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg x)]
        have hlog : Real.sqrt 2 < Real.log x :=
          lt_of_lt_of_le sqrt_two_lt_log_five (Real.log_le_log (by norm_num) (by linarith))
        have hmul : Real.sqrt 2 * Real.sqrt x ≤ Real.sqrt x * Real.log x := by
          rw [mul_comm (Real.sqrt 2)]
          exact mul_le_mul_of_nonneg_left hlog.le (Real.sqrt_nonneg x)
        linarith

/-! ### Teorema Principal -/

theorem exists_prime_in_short_interval
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 4 ≤ x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + Real.sqrt x * Real.log x := by
  by_cases hbig : 10^5 ≤ x
  · by_contra hNoPrime
    push Not at hNoPrime
    have hNoPrime' : ∀ p : ℕ, Nat.Prime p → ¬ (x < (p : ℝ) ∧ (p : ℝ) ≤ x + Real.sqrt x * Real.log x) := by
      intro p hp ⟨h1, h2⟩
      exact absurd h2 (not_le.mpr (hNoPrime p hp h1))
    have hLower := explicit_formula_triKernel_lower_bound hRH hbig
    have hUpper := prime_powers_upper_bound hbig rfl hNoPrime'
    have hMargin := analytic_margin_pos hbig
    linarith
  · exact exists_prime_small hx (lt_of_not_ge hbig)

end ShortIntervalPrimes

/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

section Chap05
section Section05

open Set Filter Real
open BigOperators
open scoped BigOperators

/-- Definition 5.5.1. For a function `f : [a, b) → ℝ` that is Riemann integrable
on every `[a, c]` with `c < b`, we define `∫ a^b f` as the limit
`lim_{c → b⁻} ∫ a^c f` when it exists. For `f : [a, ∞) → ℝ`, integrable on
every `[a, c]`, we define `∫ a^∞ f` as `lim_{c → ∞} ∫ a^c f`. The improper
integral converges if the relevant limit exists and diverges otherwise. The
analogous definitions for a left-hand endpoint are similar. -/
def ImproperIntegralRight (f : ℝ → ℝ) (a b l : ℝ) : Prop :=
  (∀ c, c < b → MeasureTheory.IntegrableOn f (Set.Icc a c)) ∧
    Tendsto (fun c : ℝ => ∫ x in a..c, f x) (nhdsWithin b (Set.Iio b)) (nhds l)

/-- Improper integral over `[a, ∞)` converging to `l`. -/
def ImproperIntegralAtTop (f : ℝ → ℝ) (a l : ℝ) : Prop :=
  (∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c)) ∧
    Tendsto (fun c : ℝ => ∫ x in a..c, f x) atTop (nhds l)

/-- Convergence of an improper integral on `[a, b)`. -/
def ImproperIntegralRightConverges (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ l, ImproperIntegralRight f a b l

/-- Convergence of an improper integral on `[a, ∞)`. -/
def ImproperIntegralAtTopConverges (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ l, ImproperIntegralAtTop f a l

/-- Helper: `x ↦ 1 / x^p` is integrable on any interval `[1, c]`. -/
lemma integrableOn_Icc_one_div_rpow (p c : ℝ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 1 / x ^ p) (Set.Icc (1 : ℝ) c) := by
  by_cases h : (1 : ℝ) ≤ c
  · have hc : 0 < c := lt_of_lt_of_le zero_lt_one h
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) c := Set.notMem_uIcc_of_lt zero_lt_one hc
    have hInt :
        IntervalIntegrable (fun x : ℝ => x ^ (-p)) MeasureTheory.volume (1 : ℝ) c := by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow (μ := MeasureTheory.volume) (a := (1 : ℝ))
          (b := c) (r := -p) (Or.inr h0))
    have hIntOn :
        MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-p)) (Set.Icc (1 : ℝ) c) := by
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) h
        (ha := by simp)).mp hInt
    have hEq : EqOn (fun x : ℝ => 1 / x ^ p) (fun x : ℝ => x ^ (-p)) (Set.Icc (1 : ℝ) c) := by
      intro x hx
      have hx0 : 0 ≤ x := by linarith [hx.1]
      calc
        1 / x ^ p = (x ^ p)⁻¹ := by simp [one_div]
        _ = x ^ (-p) := by simpa using (Real.rpow_neg hx0 p).symm
    exact (MeasureTheory.integrableOn_congr_fun hEq measurableSet_Icc).2 hIntOn
  · have hc : c < (1 : ℝ) := lt_of_not_ge h
    have hcc : Set.Icc (1 : ℝ) c = ∅ := Set.Icc_eq_empty_of_lt hc
    simp [hcc]

/-- Helper: explicit interval integral for `x ↦ 1 / x^p` on positive bounds. -/
lemma improperIntegral_p_test_integral_formula {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : p ≠ 1) :
    ∫ x in a..b, 1 / x ^ p = (b ^ (1 - p) - a ^ (1 - p)) / (1 - p) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := Set.notMem_uIcc_of_lt ha hb
  have hEq : EqOn (fun x : ℝ => 1 / x ^ p) (fun x : ℝ => x ^ (-p)) (Set.uIcc a b) := by
    intro x hx
    have hx0 : 0 ≤ x := by
      have hmin : 0 ≤ min a b := le_min (le_of_lt ha) (le_of_lt hb)
      have hx' : min a b ≤ x := by
        rcases Set.mem_uIcc.mp hx with hx' | hx'
        · exact (min_le_left _ _).trans hx'.1
        · exact (min_le_right _ _).trans hx'.1
      exact le_trans hmin hx'
    calc
      1 / x ^ p = (x ^ p)⁻¹ := by simp [one_div]
      _ = x ^ (-p) := by simpa using (Real.rpow_neg hx0 p).symm
  have hIntegral :
      ∫ x in a..b, 1 / x ^ p = ∫ x in a..b, x ^ (-p) := by
    simpa using (intervalIntegral.integral_congr (μ := MeasureTheory.volume) hEq)
  have hRpow :
      ∫ x in a..b, x ^ (-p) = (b ^ ((-p) + 1) - a ^ ((-p) + 1)) / ((-p) + 1) := by
    have hcond : (-1 : ℝ) < -p ∨ (-p ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc a b) := by
      right
      refine ⟨?_, h0⟩
      intro hpneg
      apply hp
      linarith [hpneg]
    simpa using (integral_rpow (a := a) (b := b) (r := -p) hcond)
  calc
    ∫ x in a..b, 1 / x ^ p = ∫ x in a..b, x ^ (-p) := hIntegral
    _ = (b ^ ((-p) + 1) - a ^ ((-p) + 1)) / ((-p) + 1) := hRpow
    _ = (b ^ (1 - p) - a ^ (1 - p)) / (1 - p) := by
      simp [sub_eq_add_neg, add_comm]

/-- Proposition 5.5.2 (`p`-test for integrals). The improper integral
`∫₁^∞ x^{-p}` converges to `1 / (p - 1)` for `p > 1` and diverges for
`0 < p ≤ 1`. The improper integral `∫₀^1 x^{-p}` converges to
`1 / (1 - p)` for `0 < p < 1` and diverges for `p ≥ 1`. -/
theorem improperIntegral_p_test (p : ℝ) :
    (p > 1 → ImproperIntegralAtTop (fun x : ℝ => 1 / x ^ p) 1 (1 / (p - 1))) ∧
      (0 < p → p ≤ 1 → ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / x ^ p) 1) ∧
      (0 < p → p < 1 →
        Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / (1 - p)))) ∧
      (p ≥ 1 → ¬ ∃ l : ℝ,
        Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds l)) :=
by
  refine ⟨?h1, ?h2, ?h3, ?h4⟩
  · intro hp1
    refine ⟨?hInt, ?hTend⟩
    · intro c
      exact integrableOn_Icc_one_div_rpow p c
    · have hpne : p ≠ 1 := by linarith
      have hEq :
          (fun c : ℝ => ∫ x in 1..c, 1 / x ^ p) =ᶠ[atTop]
            fun c => (c ^ (1 - p) - 1) / (1 - p) := by
        refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
        intro c hc
        simpa using
          (improperIntegral_p_test_integral_formula (a := (1 : ℝ)) (b := c) (p := p)
            zero_lt_one hc hpne)
      have hpow : Tendsto (fun c : ℝ => c ^ (1 - p)) atTop (nhds 0) := by
        have hpos : 0 < p - 1 := by linarith
        have hpow' : Tendsto (fun c : ℝ => c ^ (-(p - 1))) atTop (nhds 0) :=
          tendsto_rpow_neg_atTop hpos
        simpa [neg_sub] using hpow'
      have hsub : Tendsto (fun c : ℝ => c ^ (1 - p) - 1) atTop (nhds (-1)) := by
        simpa using (hpow.sub tendsto_const_nhds)
      have hdiv :
          Tendsto (fun c : ℝ => (c ^ (1 - p) - 1) / (1 - p)) atTop
            (nhds (-1 / (1 - p))) :=
        hsub.div_const (1 - p)
      have hval : (-1 : ℝ) / (1 - p) = 1 / (p - 1) := by
        have hden : (1 - p) ≠ 0 := by linarith
        have hden' : (p - 1) ≠ 0 := by linarith
        field_simp [hden, hden']
        ring
      exact (by simpa [hval] using (hdiv.congr' hEq.symm))
  · intro hp0 hp_le
    by_cases h1 : p = 1
    · subst h1
      intro hconv
      rcases hconv with ⟨l, hl⟩
      have hEq :
          (fun c : ℝ => ∫ x in 1..c, 1 / x) =ᶠ[atTop] fun c => Real.log c := by
        refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
        intro c hc
        simpa using (integral_one_div_of_pos (a := (1 : ℝ)) (b := c) zero_lt_one hc)
      have hlog :
          Tendsto (fun c : ℝ => ∫ x in 1..c, 1 / x) atTop atTop :=
        (Real.tendsto_log_atTop.congr' hEq.symm)
      exact not_tendsto_nhds_of_tendsto_atTop hlog l (by simpa using hl.2)
    · have hp_lt : p < 1 := lt_of_le_of_ne hp_le h1
      intro hconv
      rcases hconv with ⟨l, hl⟩
      have hEq :
          (fun c : ℝ => ∫ x in 1..c, 1 / x ^ p) =ᶠ[atTop]
            fun c => (c ^ (1 - p) - 1) / (1 - p) := by
        refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
        intro c hc
        simpa using
          (improperIntegral_p_test_integral_formula (a := (1 : ℝ)) (b := c) (p := p)
            zero_lt_one hc (by linarith))
      have hpow : Tendsto (fun c : ℝ => c ^ (1 - p)) atTop atTop :=
        tendsto_rpow_atTop (by linarith : 0 < 1 - p)
      have hsub : Tendsto (fun c : ℝ => c ^ (1 - p) - 1) atTop atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right atTop (-1) hpow)
      have hdiv : Tendsto (fun c : ℝ => (c ^ (1 - p) - 1) / (1 - p)) atTop atTop :=
        (hsub.atTop_div_const (sub_pos.mpr hp_lt))
      have hTend :
          Tendsto (fun c : ℝ => ∫ x in 1..c, 1 / x ^ p) atTop atTop :=
        hdiv.congr' hEq.symm
      exact not_tendsto_nhds_of_tendsto_atTop hTend l hl.2
  · intro hp0 hp_lt
    have hpne : p ≠ 1 := by linarith
    have hEq :
        (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun c => (1 - c ^ (1 - p)) / (1 - p) := by
      refine (eventuallyEq_of_mem
        (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_)
      intro c hc
      simpa using
        (improperIntegral_p_test_integral_formula (a := c) (b := (1 : ℝ)) (p := p)
          hc zero_lt_one hpne)
    have hpow : Tendsto (fun c : ℝ => c ^ (1 - p)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hpos : 0 < 1 - p := by linarith
      have hpow' :
          Tendsto (fun c : ℝ => (c⁻¹) ^ (p - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hpow'' :
            Tendsto (fun c : ℝ => (c⁻¹) ^ (-(1 - p))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
          (tendsto_rpow_neg_atTop hpos).comp
            (tendsto_inv_nhdsGT_zero :
              Tendsto (fun x : ℝ => x⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop)
        simpa [neg_sub] using hpow''
      have hEq :
          (fun c : ℝ => (c⁻¹) ^ (p - 1)) = fun c => c ^ (1 - p) := by
        funext c
        calc
          (c⁻¹) ^ (p - 1) = (c⁻¹) ^ (-(1 - p)) := by
            have hExp : p - 1 = -(1 - p) := by ring
            rw [hExp]
          _ = (c⁻¹)⁻¹ ^ (1 - p) := by
            simpa using (Real.rpow_neg_eq_inv_rpow (c⁻¹) (1 - p))
          _ = c ^ (1 - p) := by simp
      simpa [hEq] using hpow'
    have hsub :
        Tendsto (fun c : ℝ => 1 - c ^ (1 - p)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hpow
    have hdiv :
        Tendsto (fun c : ℝ => (1 - c ^ (1 - p)) / (1 - p)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((1 - 0) / (1 - p))) :=
      hsub.div_const (1 - p)
    have hlim :
        Tendsto (fun c : ℝ => (1 - c ^ (1 - p)) / (1 - p)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (1 / (1 - p))) := by
      simpa using hdiv
    exact hlim.congr' hEq.symm
  · intro hp_ge
    by_cases h1 : p = 1
    · subst h1
      intro hconv
      rcases hconv with ⟨l, hl⟩
      have hEq :
          (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
            fun c => -Real.log c := by
        refine (eventuallyEq_of_mem
          (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_)
        intro c hc
        have hlog : ∫ x in c..(1 : ℝ), 1 / x = Real.log (1 / c) := by
          simpa using (integral_one_div_of_pos (a := c) (b := (1 : ℝ)) hc zero_lt_one)
        simpa [one_div, Real.log_inv] using hlog
      have hlog :
          Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
        (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr' hEq.symm
      exact not_tendsto_nhds_of_tendsto_atTop hlog l (by simpa using hl)
    · have hp_gt : 1 < p := lt_of_le_of_ne hp_ge (Ne.symm h1)
      intro hconv
      rcases hconv with ⟨l, hl⟩
      have hEq :
          (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
            fun c => (1 - c ^ (1 - p)) / (1 - p) := by
        refine (eventuallyEq_of_mem
          (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_)
        intro c hc
        simpa using
          (improperIntegral_p_test_integral_formula (a := c) (b := (1 : ℝ)) (p := p)
            hc zero_lt_one (by linarith))
      have hpow :
          Tendsto (fun c : ℝ => c ^ (1 - p)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
        have hneg : 1 - p < 0 := by linarith
        simpa using (tendsto_rpow_neg_nhdsGT_zero (y := 1 - p) hneg)
      have hsub :
          Tendsto (fun c : ℝ => c ^ (1 - p) - 1) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right (nhdsWithin 0 (Set.Ioi 0)) (-1) hpow)
      have hdiv :
          Tendsto (fun c : ℝ => (c ^ (1 - p) - 1) / (p - 1)) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
        (hsub.atTop_div_const (sub_pos.mpr hp_gt))
      have hrew :
          (fun c : ℝ => (1 - c ^ (1 - p)) / (1 - p)) = fun c =>
            (c ^ (1 - p) - 1) / (p - 1) := by
        funext c
        have hden : (1 - p) ≠ 0 := by linarith
        have hden' : (p - 1) ≠ 0 := by linarith
        field_simp [hden, hden']
        ring
      have hTend :
          Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
        (hdiv.congr' (by simpa [hrew] using hEq.symm))
      exact not_tendsto_nhds_of_tendsto_atTop hTend l hl

/- Helper: extend local integrability on `(a, ∞)` to all right endpoints. -/
lemma integrableOn_Icc_all {f : ℝ → ℝ} {a b : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c)) :
    ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c) := by
  intro c
  by_cases hca : a < c
  · exact hInt c hca
  · have hca' : c ≤ a := le_of_not_gt hca
    have hcb : c ≤ b := le_trans hca' (le_of_lt hb)
    have hIntab : MeasureTheory.IntegrableOn f (Set.Icc a b) := hInt b hb
    exact (MeasureTheory.IntegrableOn.mono_set hIntab (by
      intro x hx
      exact ⟨hx.1, le_trans hx.2 hcb⟩))

/- Helper: for large `c`, the interval integral from `a` to `c` splits at `b`. -/
lemma eventually_eq_integral_split {f : ℝ → ℝ} {a b : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c)) :
    (fun c : ℝ => ∫ x in a..c, f x) =ᶠ[atTop]
      fun c => (∫ x in a..b, f x) + ∫ x in b..c, f x := by
  refine (eventuallyEq_of_mem (Ioi_mem_atTop b) ?_)
  intro c hc
  have hle_ab : a ≤ b := le_of_lt hb
  have hle_bc : b ≤ c := le_of_lt hc
  have hInt_ab :
      IntervalIntegrable f MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle_ab).2
      (hInt b hb)
  have hInt_ac : MeasureTheory.IntegrableOn f (Set.Icc a c) :=
    hInt c (lt_trans hb hc)
  have hInt_bc :
      IntervalIntegrable f MeasureTheory.volume b c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle_bc).2
      (MeasureTheory.IntegrableOn.mono_set hInt_ac (by
        intro x hx
        exact ⟨(le_trans hle_ab hx.1), hx.2⟩))
  simpa using (intervalIntegral.integral_add_adjacent_intervals hInt_ab hInt_bc).symm

/- Helper: convergence of the tail from `b` implies convergence from `a`. -/
lemma improperIntegralAtTop_of_tail {f : ℝ → ℝ} {a b l : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hbConv : ImproperIntegralAtTop f b l) :
    ImproperIntegralAtTop f a ((∫ x in a..b, f x) + l) := by
  refine ⟨integrableOn_Icc_all hb hInt, ?_⟩
  have hEq := eventually_eq_integral_split (f := f) (a := a) (b := b) hb hInt
  have hTend :
      Tendsto (fun c : ℝ => (∫ x in a..b, f x) + ∫ x in b..c, f x) atTop
        (nhds ((∫ x in a..b, f x) + l)) :=
    tendsto_const_nhds.add hbConv.2
  exact hTend.congr' hEq.symm

/- Helper: convergence from `a` implies convergence of the tail from `b`. -/
lemma improperIntegralAtTop_tail_of {f : ℝ → ℝ} {a b l : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (ha : ImproperIntegralAtTop f a l) :
    ImproperIntegralAtTop f b (l - ∫ x in a..b, f x) := by
  refine ⟨?hIntb, ?hTend⟩
  · have hInta : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c) := ha.1
    have hIntab : MeasureTheory.IntegrableOn f (Set.Icc a b) := hInta b
    intro c
    by_cases hbc : b < c
    · have hIntac : MeasureTheory.IntegrableOn f (Set.Icc a c) := hInta c
      exact (MeasureTheory.IntegrableOn.mono_set hIntac (by
        intro x hx
        exact ⟨(le_trans (le_of_lt hb) hx.1), hx.2⟩))
    · have hcb : c ≤ b := le_of_not_gt hbc
      exact (MeasureTheory.IntegrableOn.mono_set hIntab (by
        intro x hx
        exact ⟨(le_trans (le_of_lt hb) hx.1), le_trans hx.2 hcb⟩))
  · have hEq :
        (fun c : ℝ => ∫ x in b..c, f x) =ᶠ[atTop]
          fun c => (∫ x in a..c, f x) - ∫ x in a..b, f x := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop b) ?_)
      intro c hc
      have hle_ab : a ≤ b := le_of_lt hb
      have hle_bc : b ≤ c := le_of_lt hc
      have hInt_ab :
          IntervalIntegrable f MeasureTheory.volume a b :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle_ab).2
          (hInt b hb)
      have hInt_ac : MeasureTheory.IntegrableOn f (Set.Icc a c) :=
        hInt c (lt_trans hb hc)
      have hInt_bc :
          IntervalIntegrable f MeasureTheory.volume b c :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle_bc).2
          (MeasureTheory.IntegrableOn.mono_set hInt_ac (by
            intro x hx
            exact ⟨(le_trans hle_ab hx.1), hx.2⟩))
      have hEq' :
          (∫ x in a..b, f x) + ∫ x in b..c, f x = ∫ x in a..c, f x :=
        intervalIntegral.integral_add_adjacent_intervals hInt_ab hInt_bc
      linarith
    have hTend' :
        Tendsto (fun c : ℝ => (∫ x in a..c, f x) - ∫ x in a..b, f x) atTop
          (nhds (l - ∫ x in a..b, f x)) :=
      ha.2.sub tendsto_const_nhds
    exact hTend'.congr' hEq.symm

/-- Proposition 5.5.3. If `f : [a, ∞) → ℝ` is Riemann integrable on every
`[a, c]` with `c > a`, then for any `b > a` the improper integral `∫ b^∞ f`
converges if and only if `∫ a^∞ f` converges, and in the convergent case
`∫ a^∞ f = ∫ a..b, f + ∫ b^∞ f`. -/
theorem improperIntegral_tail_convergence {f : ℝ → ℝ} {a b : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c)) :
    ImproperIntegralAtTopConverges f b ↔ ImproperIntegralAtTopConverges f a :=
by
  constructor
  · intro hbConv
    rcases hbConv with ⟨l, hl⟩
    refine ⟨(∫ x in a..b, f x) + l, ?_⟩
    exact improperIntegralAtTop_of_tail (f := f) (a := a) (b := b) hb hInt hl
  · intro haConv
    rcases haConv with ⟨l, hl⟩
    refine ⟨l - ∫ x in a..b, f x, ?_⟩
    exact improperIntegralAtTop_tail_of (f := f) (a := a) (b := b) hb hInt hl

/-- Proposition 5.5.3 (value identity). Under the same hypotheses as
`improperIntegral_tail_convergence`, if the improper integrals from `a` and
from `b` both converge, then the value from `a` splits as the sum of the
integral over `[a, b]` and the improper integral from `b` to `∞`. -/
theorem improperIntegral_tail_value {f : ℝ → ℝ} {a b l₁ l₂ : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (ha : ImproperIntegralAtTop f a l₁) (hbConv : ImproperIntegralAtTop f b l₂) :
    l₁ = (∫ x in a..b, f x) + l₂ :=
by
  have ha' :
      ImproperIntegralAtTop f a ((∫ x in a..b, f x) + l₂) :=
    improperIntegralAtTop_of_tail (f := f) (a := a) (b := b) hb hInt hbConv
  exact tendsto_nhds_unique ha.2 ha'.2

/- Helper: partial integrals are monotone in the upper bound for nonnegative `f`. -/
lemma intervalIntegral_mono_upper {f : ℝ → ℝ} {a s t : ℝ}
    (hInt : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hpos : ∀ x, a ≤ x → 0 ≤ f x)
    (has : a ≤ s) (hst : s ≤ t) :
    ∫ x in a..s, f x ≤ ∫ x in a..t, f x := by
  have hat : a ≤ t := le_trans has hst
  have hInt_at :
      IntervalIntegrable f MeasureTheory.volume a t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hat).2 (hInt t)
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc a t)] f := by
    refine MeasureTheory.ae_restrict_of_forall_mem (μ := MeasureTheory.volume)
      (measurableSet_Ioc) ?_
    intro x hx
    exact hpos x (le_of_lt hx.1)
  simpa using
    (intervalIntegral.integral_mono_interval (a := a) (b := s) (c := a) (d := t)
      (hca := le_rfl) (hab := has) (hbd := hst) hnonneg hInt_at)

/- Helper: `t ↦ ∫ a..max t a f` is monotone. -/
lemma monotone_integral_max {f : ℝ → ℝ} {a : ℝ}
    (hInt : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hpos : ∀ x, a ≤ x → 0 ≤ f x) :
    Monotone (fun t : ℝ => ∫ x in a..max t a, f x) := by
  intro s t hst
  have has : a ≤ max s a := le_max_right _ _
  have hst' : max s a ≤ max t a := max_le_max hst le_rfl
  exact intervalIntegral_mono_upper (f := f) (a := a)
    (hInt := hInt) (hpos := hpos) has hst'

/- Helper: max-truncated partial integrals tend to the improper integral value. -/
lemma tendsto_integral_max {f : ℝ → ℝ} {a l : ℝ}
    (hconv : ImproperIntegralAtTop f a l) :
    Tendsto (fun t : ℝ => ∫ x in a..max t a, f x) atTop (nhds l) := by
  have hEq :
      (fun t : ℝ => ∫ x in a..max t a, f x) =ᶠ[atTop]
        fun t => ∫ x in a..t, f x := by
    refine (eventuallyEq_of_mem (Ioi_mem_atTop a) ?_)
    intro t ht
    have ht' : a ≤ t := le_of_lt (by simpa using ht)
    simp [max_eq_left ht']
  exact hconv.2.congr' hEq.symm

/- Helper: range of the max-truncated integral matches the image over `t ≥ a`. -/
lemma range_integral_max_eq_image {f : ℝ → ℝ} {a : ℝ} :
    Set.range (fun t : ℝ => ∫ x in a..max t a, f x) =
      (fun t : ℝ => ∫ x in a..t, f x) '' {t : ℝ | a ≤ t} := by
  ext y; constructor
  · rintro ⟨t, rfl⟩
    refine ⟨max t a, ?_, rfl⟩
    exact le_max_right t a
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ?_⟩
    have ht' : a ≤ t := by simpa using ht
    simp [max_eq_left ht']

/- Helper: composing with a sequence tending to `∞` preserves the limit. -/
lemma tendsto_integral_comp_seq {f : ℝ → ℝ} {a l : ℝ} {x : ℕ → ℝ}
    (hconv : ImproperIntegralAtTop f a l) (hx : Tendsto x atTop atTop) :
    Tendsto (fun n => ∫ t in a..x n, f t) atTop (nhds l) :=
  hconv.2.comp hx

/-- Proposition 5.5.4. Let `f : [a, ∞) → ℝ` be nonnegative and Riemann
integrable on every interval `[a, b]` with `b > a`.
(i) If the improper integral `∫ a^∞ f` converges to `l`, then
`l = sup {∫ a..x, f x | x ≥ a}`.
(ii) For any sequence `xₙ → ∞`, the improper integral converges if and only if
`lim_{n → ∞} ∫ a^{xₙ} f` exists, and in that case the two limits agree. -/
theorem improperIntegral_nonneg_sup_and_seq {f : ℝ → ℝ} {a l : ℝ}
    (hInt : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hpos : ∀ x, a ≤ x → 0 ≤ f x)
    (hconv : ImproperIntegralAtTop f a l) :
    l = sSup ((fun t : ℝ => ∫ x in a..t, f x) '' {t : ℝ | a ≤ t}) ∧
      ∀ x : ℕ → ℝ,
        Tendsto x atTop atTop →
          (ImproperIntegralAtTop f a l ↔
            Tendsto (fun n => ∫ t in a..x n, f t) atTop (nhds l)) :=
by
  let g : ℝ → ℝ := fun t => ∫ x in a..max t a, f x
  have hmono : Monotone g :=
    monotone_integral_max (f := f) (a := a) hInt hpos
  have hTend : Tendsto g atTop (nhds l) :=
    tendsto_integral_max (f := f) (a := a) hconv
  have hIsLUB : IsLUB (Set.range g) l :=
    isLUB_of_tendsto_atTop hmono hTend
  have hRange :
      Set.range g =
        (fun t : ℝ => ∫ x in a..t, f x) '' {t : ℝ | a ≤ t} := by
    simpa [g] using (range_integral_max_eq_image (f := f) (a := a))
  refine ⟨?_, ?_⟩
  · have hne : (Set.range g).Nonempty := ⟨g a, ⟨a, rfl⟩⟩
    simpa [hRange] using (hIsLUB.csSup_eq hne).symm
  · intro x hx
    constructor
    · intro _
      exact tendsto_integral_comp_seq (f := f) (a := a) (l := l) hconv hx
    · intro _
      exact hconv

/- Helper: comparison bound implies `g` is nonnegative on `[a, ∞)`. -/
lemma comparison_nonneg_g {a : ℝ} {f g : ℝ → ℝ}
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x) :
    ∀ x, a ≤ x → 0 ≤ g x := by
  intro x hx
  exact le_trans (abs_nonneg _) (hbound x hx)

/- Helper: difference of partial integrals is the tail integral. -/
lemma integral_diff_eq_interval {a b c : ℝ} {f : ℝ → ℝ}
    (hIntf : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hb : a ≤ b) (hbc : b ≤ c) :
    (∫ x in a..c, f x) - (∫ x in a..b, f x) = ∫ x in b..c, f x := by
  have hInt_ac : MeasureTheory.IntegrableOn f (Set.Icc a c) := hIntf c
  have hInt_bc : MeasureTheory.IntegrableOn f (Set.Icc b c) := by
    refine MeasureTheory.IntegrableOn.mono_set hInt_ac ?_
    intro x hx
    exact ⟨le_trans hb hx.1, hx.2⟩
  have hInt_ab :
      IntervalIntegrable f MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hb).2 (hIntf b)
  have hInt_bc' :
      IntervalIntegrable f MeasureTheory.volume b c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hbc).2 hInt_bc
  have hEq := intervalIntegral.integral_add_adjacent_intervals hInt_ab hInt_bc'
  linarith

/- Helper: domination by `g` bounds absolute interval integrals. -/
lemma abs_integral_le_of_bound {a : ℝ} {f g : ℝ → ℝ}
    (hIntg : ∀ c, MeasureTheory.IntegrableOn g (Set.Icc a c))
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x) :
    ∀ {c}, a ≤ c → |∫ x in a..c, f x| ≤ ∫ x in a..c, g x := by
  intro c hc
  have hIntg' :
      IntervalIntegrable g MeasureTheory.volume a c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hc).2 (hIntg c)
  have hbound_ae :
      ∀ᵐ t ∂(MeasureTheory.volume), t ∈ Set.Ioc a c → ‖f t‖ ≤ g t := by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht' : a ≤ t := le_of_lt ht.1
    simpa [Real.norm_eq_abs] using (hbound t ht')
  have hle :
      ‖∫ x in a..c, f x‖ ≤ ∫ x in a..c, g x := by
    simpa using
      (intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (a := a) (b := c)
        (f := f) (g := g) hc hbound_ae hIntg')
  simpa [Real.norm_eq_abs] using hle

/- Helper: difference of partial integrals is controlled by `g`. -/
lemma abs_integral_diff_le {a : ℝ} {f g : ℝ → ℝ}
    (hIntf : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hIntg : ∀ c, MeasureTheory.IntegrableOn g (Set.Icc a c))
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x) :
    ∀ {b c}, a ≤ b → b ≤ c →
      |(∫ x in a..c, f x) - (∫ x in a..b, f x)| ≤ ∫ x in b..c, g x := by
  intro b c hb hbc
  have hEq :
      (∫ x in a..c, f x) - (∫ x in a..b, f x) = ∫ x in b..c, f x :=
    integral_diff_eq_interval (hIntf := hIntf) hb hbc
  have hbound_b : ∀ x, b ≤ x → |f x| ≤ g x := by
    intro x hx
    exact hbound x (le_trans hb hx)
  have hIntg_b : ∀ d, MeasureTheory.IntegrableOn g (Set.Icc b d) := by
    intro d
    have hInt_ad : MeasureTheory.IntegrableOn g (Set.Icc a d) := hIntg d
    exact MeasureTheory.IntegrableOn.mono_set hInt_ad (by
      intro x hx
      exact ⟨le_trans hb hx.1, hx.2⟩)
  have hle := abs_integral_le_of_bound (a := b) (f := f) (g := g) hIntg_b hbound_b (c := c) hbc
  simpa [hEq] using hle

/- Helper: dominated partial integrals form a Cauchy filter. -/
lemma cauchy_partial_integrals_of_comparison {a : ℝ} {f g : ℝ → ℝ} {lg : ℝ}
    (hIntf : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hIntg : ∀ c, MeasureTheory.IntegrableOn g (Set.Icc a c))
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x)
    (hconv : ImproperIntegralAtTop g a lg) :
    Cauchy (Filter.map (fun c : ℝ => ∫ x in a..c, f x) atTop) := by
  let F : ℝ → ℝ := fun c => ∫ x in a..c, f x
  let G : ℝ → ℝ := fun c => ∫ x in a..c, g x
  have hG : Tendsto G atTop (nhds lg) := hconv.2
  have hGdiff :
      Tendsto (fun p : ℝ × ℝ => G p.1 - G p.2) (atTop ×ˢ atTop) (nhds (lg - lg)) :=
    (hG.comp tendsto_fst).sub (hG.comp tendsto_snd)
  have hGabs :
      Tendsto (fun p : ℝ × ℝ => |G p.1 - G p.2|) (atTop ×ˢ atTop) (nhds 0) := by
    simpa using hGdiff.abs
  have hFle :
      (fun p : ℝ × ℝ => |F p.1 - F p.2|) ≤ᶠ[atTop ×ˢ atTop]
        fun p => |G p.1 - G p.2| := by
    have hmem : (Set.Ioi a : Set ℝ) ∈ (atTop : Filter ℝ) := Ioi_mem_atTop a
    have hmem_prod :
        (Set.Ioi a ×ˢ Set.Ioi a : Set (ℝ × ℝ)) ∈
          (atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ) :=
      Filter.prod_mem_prod hmem hmem
    have hEv : ∀ᶠ p in atTop ×ˢ atTop, a ≤ p.1 ∧ a ≤ p.2 := by
      refine eventually_of_mem hmem_prod ?_
      intro p hp
      exact ⟨le_of_lt hp.1, le_of_lt hp.2⟩
    refine hEv.mono ?_
    intro p hp
    have hp1 : a ≤ p.1 := hp.1
    have hp2 : a ≤ p.2 := hp.2
    have hposg : ∀ x, a ≤ x → 0 ≤ g x :=
      comparison_nonneg_g (f := f) (g := g) hbound
    cases le_total p.1 p.2 with
    | inl h12 =>
        have hdiff :
            |F p.2 - F p.1| ≤ ∫ x in p.1..p.2, g x := by
          simpa [F] using
            (abs_integral_diff_le (hIntf := hIntf) (hIntg := hIntg) (hbound := hbound)
              (b := p.1) (c := p.2) hp1 h12)
        have hEq :
            G p.2 - G p.1 = ∫ x in p.1..p.2, g x := by
          simpa [G] using
            (integral_diff_eq_interval (hIntf := hIntg) (b := p.1) (c := p.2) (a := a) hp1 h12)
        have hnonneg : 0 ≤ ∫ x in p.1..p.2, g x := by
          refine intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) (a := p.1) (b := p.2)
            h12 ?_
          intro x hx
          exact hposg x (le_trans hp1 hx.1)
        have hEqAbs : |G p.1 - G p.2| = ∫ x in p.1..p.2, g x := by
          have : |G p.2 - G p.1| = ∫ x in p.1..p.2, g x := by
            simp [hEq, abs_of_nonneg hnonneg]
          simpa [abs_sub_comm] using this
        simpa [abs_sub_comm, hEqAbs.symm] using hdiff
    | inr h21 =>
        have hdiff :
            |F p.1 - F p.2| ≤ ∫ x in p.2..p.1, g x := by
          simpa [F, abs_sub_comm] using
            (abs_integral_diff_le (hIntf := hIntf) (hIntg := hIntg) (hbound := hbound)
              (b := p.2) (c := p.1) hp2 h21)
        have hEq :
            G p.1 - G p.2 = ∫ x in p.2..p.1, g x := by
          simpa [G] using
            (integral_diff_eq_interval (hIntf := hIntg) (b := p.2) (c := p.1) (a := a) hp2 h21)
        have hnonneg : 0 ≤ ∫ x in p.2..p.1, g x := by
          refine intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) (a := p.2) (b := p.1)
            h21 ?_
          intro x hx
          exact hposg x (le_trans hp2 hx.1)
        have hEqAbs : |G p.1 - G p.2| = ∫ x in p.2..p.1, g x := by
          simp [hEq, abs_of_nonneg hnonneg]
        exact hdiff.trans_eq hEqAbs.symm
  have hLower :
      (fun p : ℝ × ℝ => -|G p.1 - G p.2|) ≤ᶠ[atTop ×ˢ atTop]
        fun p => F p.1 - F p.2 := by
    refine hFle.mono ?_
    intro p hp
    exact (abs_le.mp hp).1
  have hUpper :
      (fun p : ℝ × ℝ => F p.1 - F p.2) ≤ᶠ[atTop ×ˢ atTop]
        fun p => |G p.1 - G p.2| := by
    refine hFle.mono ?_
    intro p hp
    exact (abs_le.mp hp).2
  have hDiff :
      Tendsto (fun p : ℝ × ℝ => F p.1 - F p.2) (atTop ×ˢ atTop) (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hGabs.neg) hGabs hLower hUpper
  refine (IsUniformAddGroup.cauchy_map_iff_tendsto (𝓕 := atTop) (f := F)).2 ?_
  exact ⟨by infer_instance, hDiff⟩

/- Helper: pass eventual absolute bounds to the limit. -/
lemma limit_abs_le {F G : ℝ → ℝ} {lf lg : ℝ}
    (hF : Tendsto F atTop (nhds lf))
    (hG : Tendsto G atTop (nhds lg))
    (hbound : ∀ᶠ x in atTop, |F x| ≤ G x) :
    |lf| ≤ lg := by
  have hFabs : Tendsto (fun x => |F x|) atTop (nhds |lf|) := hF.abs
  exact tendsto_le_of_eventuallyLE hFabs hG hbound

/-- Proposition 5.5.5 (comparison test for improper integrals). Let
`f g : [a, ∞) → ℝ` be Riemann integrable on every `[a, b]` with `b > a` and
assume `|f x| ≤ g x` for all `x ≥ a`.
(i) If `∫ a^∞ g` converges, then `∫ a^∞ f` converges and
`|∫ a^∞ f| ≤ ∫ a^∞ g`.
(ii) If `∫ a^∞ f` diverges, then `∫ a^∞ g` diverges. -/
theorem improperIntegral_comparison {a : ℝ} {f g : ℝ → ℝ}
    (hIntf : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hIntg : ∀ c, MeasureTheory.IntegrableOn g (Set.Icc a c))
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x) :
    (∀ {lg : ℝ}, ImproperIntegralAtTop g a lg →
      ∃ lf : ℝ, ImproperIntegralAtTop f a lf ∧ |lf| ≤ lg) ∧
      (¬ ImproperIntegralAtTopConverges f a → ¬ ImproperIntegralAtTopConverges g a) :=
by
  have h1 :
      ∀ {lg : ℝ}, ImproperIntegralAtTop g a lg →
        ∃ lf : ℝ, ImproperIntegralAtTop f a lf ∧ |lf| ≤ lg := by
    intro lg hconv
    let F : ℝ → ℝ := fun c => ∫ x in a..c, f x
    let G : ℝ → ℝ := fun c => ∫ x in a..c, g x
    have hCauchy :
        Cauchy (Filter.map (fun c : ℝ => ∫ x in a..c, f x) atTop) :=
      cauchy_partial_integrals_of_comparison (hIntf := hIntf) (hIntg := hIntg)
        (hbound := hbound) hconv
    have hExists : ∃ lf, Tendsto F atTop (nhds lf) :=
      (cauchy_map_iff_exists_tendsto (l := atTop) (f := F)).1 hCauchy
    rcases hExists with ⟨lf, hF⟩
    have hF' : Tendsto (fun c : ℝ => ∫ x in a..c, f x) atTop (nhds lf) := by
      simpa [F] using hF
    have hFle : ∀ᶠ x in atTop, |F x| ≤ G x := by
      refine (eventually_of_mem (Ioi_mem_atTop a) ?_)
      intro x hx
      have hx' : a ≤ x := le_of_lt hx
      simpa [F, G] using
        (abs_integral_le_of_bound (a := a) (f := f) (g := g) hIntg hbound (c := x) hx')
    have hAbs : |lf| ≤ lg :=
      limit_abs_le (F := F) (G := G) (lf := lf) (lg := lg) hF hconv.2 hFle
    refine ⟨lf, ?_, hAbs⟩
    exact ⟨hIntf, hF'⟩
  refine ⟨h1, ?_⟩
  intro hdiv hconv
  rcases hconv with ⟨lg, hlg⟩
  rcases (h1 hlg) with ⟨lf, hlf, _⟩
  exact hdiv ⟨lf, hlf⟩

/- Helper: local integrability of the oscillatory integrand on `[a, c]` with `0 ≤ a`. -/
lemma integrableOn_sin_sq_over_cubic_Icc {a c : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => (Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1))
      (Set.Icc a c) := by
  have hcont :
      ContinuousOn (fun x : ℝ => (Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)) (Set.Icc a c) := by
    refine (ContinuousOn.div ?hnum ?hden ?hneq)
    · have hnum' : Continuous (fun x : ℝ => Real.sin (x ^ 2) * (x + 2)) := by
        continuity
      exact hnum'.continuousOn
    · have hden' : Continuous (fun x : ℝ => x ^ 3 + 1) := by
        continuity
      exact hden'.continuousOn
    · intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1
      have hx3 : 0 ≤ x ^ 3 := by exact pow_nonneg hx0 3
      have hpos : 0 < x ^ 3 + 1 := by linarith
      exact ne_of_gt hpos
  exact hcont.integrableOn_Icc

/- Helper: tail bound for the oscillatory integrand on `[1, ∞)`. -/
lemma bound_sin_sq_over_cubic {x : ℝ} (hx : 1 ≤ x) :
    |(Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)| ≤ 3 / x ^ 2 := by
  have hx0 : 0 ≤ x := le_trans (show (0 : ℝ) ≤ 1 by linarith) hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx3pos : 0 < x ^ 3 := by exact pow_pos hxpos 3
  have hx3nonneg : 0 ≤ x ^ 3 := le_of_lt hx3pos
  have hdenpos : 0 < x ^ 3 + 1 := by linarith
  have hnum_nonneg : 0 ≤ x + 2 := by linarith
  have hnum_le : x + 2 ≤ 3 * x := by nlinarith
  calc
    |(Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)|
        = |Real.sin (x ^ 2) * (x + 2)| / (x ^ 3 + 1) := by
            simp [abs_div, abs_of_pos hdenpos]
    _ = |Real.sin (x ^ 2)| * |x + 2| / (x ^ 3 + 1) := by
            simp [abs_mul]
    _ ≤ 1 * |x + 2| / (x ^ 3 + 1) := by
            gcongr
            exact Real.abs_sin_le_one (x ^ 2)
    _ = |x + 2| / (x ^ 3 + 1) := by simp
    _ = (x + 2) / (x ^ 3 + 1) := by
            simp [abs_of_nonneg hnum_nonneg]
    _ ≤ (x + 2) / (x ^ 3) := by
            exact div_le_div_of_nonneg_left hnum_nonneg hx3pos (by linarith)
    _ ≤ (3 * x) / (x ^ 3) := by
            exact div_le_div_of_nonneg_right hnum_le hx3nonneg
    _ = 3 / x ^ 2 := by
            have hx0' : x ≠ 0 := by linarith
            calc
              (3 * x) / (x ^ 3) = (x * 3) / (x * x ^ 2) := by
                simp [pow_succ, mul_comm]
              _ = 3 / x ^ 2 := by
                simpa using (mul_div_mul_left (a := 3) (b := x ^ 2) (c := x) hx0')

/- Helper: the improper integral of `3 / x^2` from `1` equals `3`. -/
lemma improperIntegralAtTop_three_over_x_sq :
    ImproperIntegralAtTop (fun x : ℝ => 3 / x ^ 2) 1 3 := by
  have hbase : ImproperIntegralAtTop (fun x : ℝ => 1 / x ^ 2) 1 (1 : ℝ) := by
    have h : (2 : ℝ) - 1 = 1 := by norm_num
    simpa [h] using (improperIntegral_p_test 2).1 (by linarith)
  refine ⟨?hInt, ?hTend⟩
  · intro c
    have hInt0 :
        MeasureTheory.IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Set.Icc (1 : ℝ) c) :=
      hbase.1 c
    have hInt1 :
        MeasureTheory.IntegrableOn (fun x : ℝ => (1 / x ^ 2) * (3 : ℝ)) (Set.Icc (1 : ℝ) c) := by
      refine hInt0.mul_continuousOn (g' := fun _ : ℝ => (3 : ℝ)) ?_ ?_
      · simpa using
          (continuousOn_const : ContinuousOn (fun _ : ℝ => (3 : ℝ)) (Set.Icc (1 : ℝ) c))
      · simpa using (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) c))
    simpa [mul_comm, div_eq_mul_inv] using hInt1
  · have hTend :
        Tendsto (fun c : ℝ => 3 * ∫ x in 1..c, 1 / x ^ 2) atTop (nhds (3 * 1)) :=
      (Filter.Tendsto.const_mul 3 hbase.2)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hTend

/-- Example 5.5.6. The improper integral
`∫₀^∞ (sin (x^2) * (x + 2)) / (x^3 + 1)` converges, for instance by comparing
its tail to `3 / x^2` on `[1, ∞)` and using the tail test. -/
theorem improperIntegral_sin_sq_over_cubic_converges :
    ImproperIntegralAtTopConverges
      (fun x : ℝ => (Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)) 0 :=
by
  let f : ℝ → ℝ := fun x => (Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)
  let g : ℝ → ℝ := fun x => 3 / x ^ 2
  have hInt0 : ∀ c > 0, MeasureTheory.IntegrableOn f (Set.Icc 0 c) := by
    intro c _
    simpa [f] using (integrableOn_sin_sq_over_cubic_Icc (a := 0) (c := c) (ha := le_rfl))
  have hInt1 : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc 1 c) := by
    intro c
    simpa [f] using
      (integrableOn_sin_sq_over_cubic_Icc (a := 1) (c := c) (ha := (by exact zero_le_one)))
  have hconv_g : ImproperIntegralAtTop g 1 3 := by
    simpa [g] using improperIntegralAtTop_three_over_x_sq
  have hbound : ∀ x, 1 ≤ x → |f x| ≤ g x := by
    intro x hx
    simpa [f, g] using (bound_sin_sq_over_cubic (x := x) hx)
  have hconv_f_tail : ImproperIntegralAtTopConverges f 1 := by
    have hcomp :
        ∀ {lg : ℝ}, ImproperIntegralAtTop g 1 lg →
          ∃ lf : ℝ, ImproperIntegralAtTop f 1 lf ∧ |lf| ≤ lg :=
      (improperIntegral_comparison (a := 1) (f := f) (g := g)
        (hIntf := hInt1) (hIntg := hconv_g.1) (hbound := hbound)).1
    rcases hcomp hconv_g with ⟨lf, hlf, _⟩
    exact ⟨lf, hlf⟩
  have htail : ImproperIntegralAtTopConverges f 0 :=
    (improperIntegral_tail_convergence (f := f) (a := 0) (b := 1)
      (hb := by linarith) (hInt := hInt0)).1 hconv_f_tail
  simpa [f] using htail

/- Helper: shifting by a constant preserves divergence to `+∞`. -/
lemma tendsto_add_const_atTop (k : ℝ) :
    Tendsto (fun x : ℝ => x + k) atTop atTop := by
  refine tendsto_atTop_atTop.mpr ?_
  intro b
  refine ⟨b - k, ?_⟩
  intro x hx
  linarith

/- Helper: integrate `1 / (x - 1)` on `(2, c)` via a shift. -/
lemma intervalIntegral_one_div_sub {c : ℝ} (hc : 2 < c) :
    ∫ x in 2..c, 1 / (x - 1) = Real.log (c - 1) := by
  have hc' : 0 < c - 1 := by linarith
  have hcomp :
      ∫ x in 2..c, 1 / (x - 1) = ∫ x in (2 : ℝ) + (-1)..c + (-1), 1 / x := by
    simp [sub_eq_add_neg]
  have hcomp' :
      ∫ x in 2..c, 1 / (x - 1) = ∫ x in (1 : ℝ)..(c - 1), 1 / x := by
    have h2 : (2 : ℝ) + (-1) = 1 := by ring
    have h3 : c + (-1) = c - 1 := by ring
    simpa [h2, h3] using hcomp
  calc
    ∫ x in 2..c, 1 / (x - 1) = ∫ x in (1 : ℝ)..(c - 1), 1 / x := hcomp'
    _ = Real.log (c - 1) := by
      simpa using
        (integral_one_div_of_pos (a := (1 : ℝ)) (b := c - 1) zero_lt_one hc')

/- Helper: integrate `1 / (x + 1)` on `(2, c)` via a shift. -/
lemma intervalIntegral_one_div_add {c : ℝ} (hc : 2 < c) :
    ∫ x in 2..c, 1 / (x + 1) = Real.log (c + 1) - Real.log 3 := by
  have hc' : 0 < c + 1 := by linarith
  have hcomp :
      ∫ x in 2..c, 1 / (x + 1) = ∫ x in (2 : ℝ) + 1..c + 1, 1 / x := by
    simp
  have hcomp' :
      ∫ x in 2..c, 1 / (x + 1) = ∫ x in (3 : ℝ)..(c + 1), 1 / x := by
    have h2 : (2 : ℝ) + 1 = 3 := by ring
    simp [h2]
  calc
    ∫ x in 2..c, 1 / (x + 1) = ∫ x in (3 : ℝ)..(c + 1), 1 / x := hcomp'
    _ = Real.log ((c + 1) / 3) := by
      have hpos3 : 0 < (3 : ℝ) := by linarith
      simpa using (integral_one_div_of_pos (a := (3 : ℝ)) (b := c + 1) hpos3 hc')
    _ = Real.log (c + 1) - Real.log 3 := by
      have hne1 : (c + 1) ≠ 0 := by linarith
      have hne3 : (3 : ℝ) ≠ 0 := by norm_num
      simpa using (Real.log_div hne1 hne3)

/- Helper: interval integrability of `1 / (x - 1)` on `[2, c]` for `c > 2`. -/
lemma intervalIntegrable_one_div_sub {c : ℝ} (hc : 2 < c) :
    IntervalIntegrable (fun x : ℝ => 1 / (x - 1)) MeasureTheory.volume 2 c := by
  have hle : (2 : ℝ) ≤ c := by linarith
  have hcont_den : ContinuousOn (fun x : ℝ => x - 1) (Set.Icc 2 c) := by
    simpa [sub_eq_add_neg] using (continuousOn_id.sub continuousOn_const)
  have hden : ∀ x ∈ Set.Icc 2 c, x - 1 ≠ 0 := by
    intro x hx
    have hxpos : 0 < x - 1 := by linarith [hx.1]
    exact ne_of_gt hxpos
  have hcont : ContinuousOn (fun x : ℝ => 1 / (x - 1)) (Set.Icc 2 c) :=
    (continuousOn_const.div hcont_den hden)
  have hIntOn :
      MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (x - 1)) (Set.Icc 2 c) :=
    hcont.integrableOn_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle).2 hIntOn

/- Helper: interval integrability of `1 / (x + 1)` on `[2, c]` for `c > 2`. -/
lemma intervalIntegrable_one_div_add {c : ℝ} (hc : 2 < c) :
    IntervalIntegrable (fun x : ℝ => 1 / (x + 1)) MeasureTheory.volume 2 c := by
  have hle : (2 : ℝ) ≤ c := by linarith
  have hcont_den : ContinuousOn (fun x : ℝ => x + 1) (Set.Icc 2 c) := by
    simpa using (continuousOn_id.add continuousOn_const)
  have hden : ∀ x ∈ Set.Icc 2 c, x + 1 ≠ 0 := by
    intro x hx
    have hxpos : 0 < x + 1 := by linarith [hx.1]
    exact ne_of_gt hxpos
  have hcont : ContinuousOn (fun x : ℝ => 1 / (x + 1)) (Set.Icc 2 c) :=
    (continuousOn_const.div hcont_den hden)
  have hIntOn :
      MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (x + 1)) (Set.Icc 2 c) :=
    hcont.integrableOn_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle).2 hIntOn

/- Helper: evaluate the partial fractions integral on `(2, c)`. -/
lemma intervalIntegral_two_over_x_sq_sub_one {c : ℝ} (hc : 2 < c) :
    ∫ x in 2..c, 2 / (x ^ 2 - 1) =
      Real.log (c - 1) - Real.log (c + 1) + Real.log 3 := by
  have hEq :
      EqOn (fun x : ℝ => 2 / (x ^ 2 - 1))
        (fun x : ℝ => 1 / (x - 1) - 1 / (x + 1)) (Set.uIcc 2 c) := by
    intro x hx
    have hx' : x ∈ Set.Icc 2 c := by
      have hIcc : Set.uIcc 2 c = Set.Icc 2 c := Set.uIcc_of_le (by linarith)
      simpa [hIcc] using hx
    have hxne1 : x - 1 ≠ 0 := by
      have hxpos : 0 < x - 1 := by linarith [hx'.1]
      exact ne_of_gt hxpos
    have hxne2 : x + 1 ≠ 0 := by
      have hxpos : 0 < x + 1 := by linarith [hx'.1]
      exact ne_of_gt hxpos
    have hxden : x ^ 2 - 1 ≠ 0 := by
      have hxpos : 0 < x ^ 2 - 1 := by nlinarith [hx'.1]
      exact ne_of_gt hxpos
    field_simp [hxden, hxne1, hxne2]
    ring
  have hEqInt :
      ∫ x in 2..c, 2 / (x ^ 2 - 1) =
        ∫ x in 2..c, (1 / (x - 1) - 1 / (x + 1)) := by
    simpa using (intervalIntegral.integral_congr (μ := MeasureTheory.volume) hEq)
  have hsplit :
      ∫ x in 2..c, (1 / (x - 1) - 1 / (x + 1)) =
        (∫ x in 2..c, 1 / (x - 1)) - ∫ x in 2..c, 1 / (x + 1) := by
    simpa using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume)
        (intervalIntegrable_one_div_sub (c := c) hc)
        (intervalIntegrable_one_div_add (c := c) hc))
  calc
    ∫ x in 2..c, 2 / (x ^ 2 - 1) =
        ∫ x in 2..c, (1 / (x - 1) - 1 / (x + 1)) := hEqInt
    _ = (∫ x in 2..c, 1 / (x - 1)) - ∫ x in 2..c, 1 / (x + 1) := hsplit
    _ = Real.log (c - 1) - ∫ x in 2..c, 1 / (x + 1) := by
      rw [intervalIntegral_one_div_sub (c := c) hc]
    _ = Real.log (c - 1) - (Real.log (c + 1) - Real.log 3) := by
      rw [intervalIntegral_one_div_add (c := c) hc]
    _ = Real.log (c - 1) - Real.log (c + 1) + Real.log 3 := by ring

/- Helper: `log (c - 1) - log (c + 1)` tends to `0` as `c → ∞`. -/
lemma tendsto_log_sub_log_zero :
    Tendsto (fun c : ℝ => Real.log (c - 1) - Real.log (c + 1)) atTop (nhds 0) := by
  have hshift : Tendsto (fun c : ℝ => c + 1) atTop atTop :=
    tendsto_add_const_atTop 1
  have h := (Real.tendsto_log_comp_add_sub_log (-2)).comp hshift
  refine h.congr' ?_
  refine (Filter.Eventually.of_forall ?_)
  intro c
  have h' : (c + 1) + (-2) = c - 1 := by ring
  simp [h', sub_eq_add_neg, add_comm]

/- Helper: the shifted reciprocal integrals diverge at `∞`. -/
lemma divergence_shifted_one_div :
    ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / (x - 1)) 2 ∧
      ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / (x + 1)) 2 := by
  refine ⟨?hsub, ?hadd⟩
  · intro hconv
    rcases hconv with ⟨l, hl⟩
    have hEq :
        (fun c : ℝ => ∫ x in 2..c, 1 / (x - 1)) =ᶠ[atTop]
          fun c => Real.log (c - 1) := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 2) ?_)
      intro c hc
      simpa using (intervalIntegral_one_div_sub (c := c) hc)
    have hshift : Tendsto (fun c : ℝ => c - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using (tendsto_add_const_atTop (-1))
    have hlog : Tendsto (fun c : ℝ => Real.log (c - 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp hshift
    have hTend :
        Tendsto (fun c : ℝ => ∫ x in 2..c, 1 / (x - 1)) atTop atTop :=
      hlog.congr' hEq.symm
    exact not_tendsto_nhds_of_tendsto_atTop hTend l (by simpa using hl.2)
  · intro hconv
    rcases hconv with ⟨l, hl⟩
    have hEq :
        (fun c : ℝ => ∫ x in 2..c, 1 / (x + 1)) =ᶠ[atTop]
          fun c => Real.log (c + 1) - Real.log 3 := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 2) ?_)
      intro c hc
      simpa using (intervalIntegral_one_div_add (c := c) hc)
    have hshift : Tendsto (fun c : ℝ => c + 1) atTop atTop :=
      tendsto_add_const_atTop 1
    have hlog : Tendsto (fun c : ℝ => Real.log (c + 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp hshift
    have hlog' : Tendsto (fun c : ℝ => Real.log (c + 1) - Real.log 3) atTop atTop := by
      simpa [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-Real.log (3 : ℝ)) hlog)
    have hTend :
        Tendsto (fun c : ℝ => ∫ x in 2..c, 1 / (x + 1)) atTop atTop :=
      hlog'.congr' hEq.symm
    exact not_tendsto_nhds_of_tendsto_atTop hTend l (by simpa using hl.2)

/- Helper: integrability of `2 / (x^2 - 1)` on `[2, c]`. -/
lemma integrableOn_two_over_x_sq_sub_one_Icc (c : ℝ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 2 / (x ^ 2 - 1)) (Set.Icc 2 c) := by
  by_cases hc : (2 : ℝ) ≤ c
  · have hcont_den : ContinuousOn (fun x : ℝ => x ^ 2 - 1) (Set.Icc 2 c) := by
      have hcont_sq : ContinuousOn (fun x : ℝ => x ^ 2) (Set.Icc 2 c) := by
        simpa [pow_two] using (continuousOn_id.mul continuousOn_id)
      simpa using hcont_sq.sub continuousOn_const
    have hden : ∀ x ∈ Set.Icc 2 c, x ^ 2 - 1 ≠ 0 := by
      intro x hx
      have hxpos : 0 < x ^ 2 - 1 := by nlinarith [hx.1]
      exact ne_of_gt hxpos
    have hcont : ContinuousOn (fun x : ℝ => 2 / (x ^ 2 - 1)) (Set.Icc 2 c) :=
      (continuousOn_const.div hcont_den hden)
    exact hcont.integrableOn_Icc
  · have hcc : Set.Icc (2 : ℝ) c = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hc)
    simp [hcc]

/-- Example 5.5.7. The improper integral `∫₂^∞ 2 / (x^2 - 1)` converges (in
fact to `log 3`), but writing `2 / (x^2 - 1) = 1 / (x - 1) - 1 / (x + 1)` does
not allow splitting the improper integral, since both pieces diverge
separately. -/
theorem improperIntegral_partial_fraction_counterexample :
    ImproperIntegralAtTop (fun x : ℝ => 2 / (x ^ 2 - 1)) 2 (Real.log (3 : ℝ)) ∧
      ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / (x - 1)) 2 ∧
      ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / (x + 1)) 2 :=
by
  refine ⟨?hconv, divergence_shifted_one_div⟩
  refine ⟨?hInt, ?hTend⟩
  · intro c
    exact integrableOn_two_over_x_sq_sub_one_Icc c
  · have hEq :
        (fun c : ℝ => ∫ x in 2..c, 2 / (x ^ 2 - 1)) =ᶠ[atTop]
          fun c => Real.log (c - 1) - Real.log (c + 1) + Real.log (3 : ℝ) := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 2) ?_)
      intro c hc
      simpa using (intervalIntegral_two_over_x_sq_sub_one (c := c) hc)
    have hTend0 :
        Tendsto (fun c : ℝ => Real.log (c - 1) - Real.log (c + 1) + Real.log (3 : ℝ)) atTop
          (nhds (Real.log (3 : ℝ))) := by
      have hlog : Tendsto (fun c : ℝ => Real.log (c - 1) - Real.log (c + 1)) atTop (nhds 0) :=
        tendsto_log_sub_log_zero
      have hconst :
          Tendsto (fun _ : ℝ => Real.log (3 : ℝ)) atTop (nhds (Real.log (3 : ℝ))) :=
        tendsto_const_nhds
      have hsum := hlog.add hconst
      simpa using hsum
    exact hTend0.congr' hEq.symm


/-- Definition 5.5.8. For a function `f : (a, b) → ℝ` that is Riemann
integrable on every closed subinterval `[c, d]` with `a < c < d < b`, the
improper integral `∫ a^b f` is defined as the iterated limit
`lim_{c → a⁺} lim_{d → b⁻} ∫_{c}^{d} f` when this limit exists. -/
def ImproperIntegralOpenInterval (f : ℝ → ℝ) (a b l : ℝ) : Prop :=
  (∀ ⦃c d⦄, a < c → c < d → d < b → MeasureTheory.IntegrableOn f (Set.Icc c d)) ∧
    Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      (nhdsWithin a (Set.Ioi a) ×ˢ nhdsWithin b (Set.Iio b)) (nhds l)

/-- Definition 5.5.8 (whole line). If `f : ℝ → ℝ` is Riemann integrable on
every bounded interval `[a, b]`, then the improper integral `∫_{-∞}^{∞} f` is
defined as `lim_{c → -∞} lim_{d → ∞} ∫_{c}^{d} f`, when this limit exists. -/
def ImproperIntegralRealLine (f : ℝ → ℝ) (l : ℝ) : Prop :=
  (∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) ∧
    Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (Filter.atBot ×ˢ Filter.atTop) (nhds l)

/- Helper: integrability of `x ↦ 1 / (1 + x^2)` on any closed interval. -/
lemma integrableOn_inv_one_plus_sq_Icc (a b : ℝ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (1 + x ^ 2)) (Set.Icc a b) := by
  simpa [one_div] using (integrable_inv_one_add_sq.integrableOn (s := Set.Icc a b))

/- Helper: interval integral of `1 / (1 + x^2)` via `arctan`. -/
lemma intervalIntegral_inv_one_add_sq_eq_arctan (a b : ℝ) :
    (∫ x in a..b, 1 / (1 + x ^ 2)) = arctan b - arctan a := by
  simp [one_div]

/- Helper: `arctan` difference tends to `π` on `(-∞, ∞)`. -/
lemma tendsto_arctan_diff_atBot_atTop :
    Tendsto (fun p : ℝ × ℝ => arctan p.2 - arctan p.1) (Filter.atBot ×ˢ Filter.atTop)
      (nhds (π : ℝ)) := by
  have htop : Tendsto arctan atTop (nhds (π / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop
  have hbot : Tendsto arctan atBot (nhds (-(π / 2))) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot
  have hsnd :
      Tendsto (fun p : ℝ × ℝ => arctan p.2) (Filter.atBot ×ˢ Filter.atTop) (nhds (π / 2)) :=
    htop.comp tendsto_snd
  have hfst :
      Tendsto (fun p : ℝ × ℝ => arctan p.1) (Filter.atBot ×ˢ Filter.atTop)
        (nhds (-(π / 2))) :=
    hbot.comp tendsto_fst
  have hsub := hsnd.sub hfst
  have hpi : (π / 2) - (-(π / 2)) = (π : ℝ) := by ring
  simpa [hpi] using hsub

/-- Example 5.5.9. The improper integral of `1 / (1 + x^2)` over the entire real
line converges and has value `π`, computed via the antiderivative `x ↦ arctan x`
and the limits at `±∞`. -/
theorem improperIntegral_real_line_inv_one_plus_sq :
    ImproperIntegralRealLine (fun x : ℝ => 1 / (1 + x ^ 2)) Real.pi :=
by
  refine ⟨?hInt, ?hTend⟩
  · intro a b
    exact integrableOn_inv_one_plus_sq_Icc a b
  · have hEq :
        (fun p : ℝ × ℝ => ∫ x in p.1..p.2, 1 / (1 + x ^ 2)) =ᶠ[Filter.atBot ×ˢ Filter.atTop]
          fun p => arctan p.2 - arctan p.1 := by
      refine Filter.Eventually.of_forall ?_
      intro p
      exact intervalIntegral_inv_one_add_sq_eq_arctan p.1 p.2
    have hTend :
        Tendsto (fun p : ℝ × ℝ => arctan p.2 - arctan p.1) (Filter.atBot ×ˢ Filter.atTop)
          (nhds (Real.pi)) := by
      simpa using tendsto_arctan_diff_atBot_atTop
    exact hTend.congr' hEq.symm

/-- Helper: integrability on all closed intervals implies interval integrability. -/
lemma intervalIntegrable_of_integrableOn_Icc {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) (a b : ℝ) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  by_cases hab : a ≤ b
  · exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hab).2
        (hInt a b)
  · have hba : b ≤ a := le_of_not_ge hab
    have hba' :
        IntervalIntegrable f MeasureTheory.volume b a :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hba).2
        (hInt b a)
    exact hba'.symm

/-- Helper: express an interval integral via the basepoint `0`. -/
lemma intervalIntegral_eq_sub_base {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) (a b : ℝ) :
    (∫ x in a..b, f x) = (∫ x in 0..b, f x) - (∫ x in 0..a, f x) := by
  have hInt0a : IntervalIntegrable f MeasureTheory.volume 0 a :=
    intervalIntegrable_of_integrableOn_Icc hInt 0 a
  have hIntab : IntervalIntegrable f MeasureTheory.volume a b :=
    intervalIntegrable_of_integrableOn_Icc hInt a b
  have hEq :
      (∫ x in 0..a, f x) + ∫ x in a..b, f x = ∫ x in 0..b, f x :=
    intervalIntegral.integral_add_adjacent_intervals hInt0a hIntab
  linarith

/-- Helper: convergence of base integrals at `-∞` gives left partial limits. -/
lemma tendsto_intervalIntegral_atBot_of_base {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) {Lminus : ℝ}
    (hbot : Tendsto (fun t : ℝ => ∫ x in 0..t, f x) atBot (nhds Lminus)) (b : ℝ) :
    Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds ((∫ x in 0..b, f x) - Lminus)) := by
  have hEq :
      (fun a : ℝ => ∫ x in a..b, f x) =ᶠ[atBot]
        fun a => (∫ x in 0..b, f x) - (∫ x in 0..a, f x) := by
    refine Filter.Eventually.of_forall ?_
    intro a
    simpa using intervalIntegral_eq_sub_base (f := f) hInt a b
  have hconst :
      Tendsto (fun _ : ℝ => ∫ x in 0..b, f x) atBot (nhds (∫ x in 0..b, f x)) :=
    tendsto_const_nhds
  have hsub := hconst.sub hbot
  exact hsub.congr' hEq.symm

/-- Helper: base limits at `±∞` yield the two-variable limit. -/
lemma tendsto_intervalIntegral_atBot_atTop_of_base {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b))
    {Lminus Lplus : ℝ}
    (hbot : Tendsto (fun t : ℝ => ∫ x in 0..t, f x) atBot (nhds Lminus))
    (htop : Tendsto (fun t : ℝ => ∫ x in 0..t, f x) atTop (nhds Lplus)) :
    Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (Filter.atBot ×ˢ Filter.atTop)
      (nhds (Lplus - Lminus)) := by
  have hEq :
      (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) =ᶠ[Filter.atBot ×ˢ Filter.atTop]
        fun p => (∫ x in 0..p.2, f x) - (∫ x in 0..p.1, f x) := by
    refine Filter.Eventually.of_forall ?_
    intro p
    simpa using intervalIntegral_eq_sub_base (f := f) hInt p.1 p.2
  have hsnd :
      Tendsto (fun p : ℝ × ℝ => ∫ x in 0..p.2, f x) (Filter.atBot ×ˢ Filter.atTop)
        (nhds Lplus) :=
    htop.comp tendsto_snd
  have hfst :
      Tendsto (fun p : ℝ × ℝ => ∫ x in 0..p.1, f x) (Filter.atBot ×ˢ Filter.atTop)
        (nhds Lminus) :=
    hbot.comp tendsto_fst
  have hsub := hsnd.sub hfst
  exact hsub.congr' hEq.symm

/-- Proposition 5.5.10. If `f : ℝ → ℝ` is Riemann integrable on every bounded
interval `[a, b]`, then the iterated limits
`lim_{a → -∞} lim_{b → ∞} ∫_{a}^{b} f` and
`lim_{b → ∞} lim_{a → -∞} ∫_{a}^{b} f` converge together and have the same
value. If either iterated limit exists, then the improper integral over the
whole line converges to the same value and agrees with the limit of the
symmetric integrals `∫_{-a}^{a} f` as `a → ∞`. -/
theorem improperIntegral_iterated_limits_symm {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) :
    ((∃ g l,
        (∀ a, Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds (g a))) ∧
        Tendsto g atBot (nhds l)) ↔
      (∃ h l,
        (∀ b, Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b))) ∧
        Tendsto h atTop (nhds l)))
    ∧
      (∀ g h l₁ l₂,
        (∀ a, Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds (g a))) →
        Tendsto g atBot (nhds l₁) →
        (∀ b, Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b))) →
        Tendsto h atTop (nhds l₂) →
        l₁ = l₂)
    ∧
      ((∃ g l,
        (∀ a, Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds (g a))) ∧
        Tendsto g atBot (nhds l)) →
        ∃ l,
          ImproperIntegralRealLine f l ∧
            Tendsto (fun a : ℝ => ∫ x in (-a)..a, f x) atTop (nhds l)) :=
by
  classical
  let F : ℝ → ℝ := fun t => ∫ x in 0..t, f x
  have hEqInt : ∀ a b, ∫ x in a..b, f x = F b - F a := by
    intro a b
    simpa [F] using intervalIntegral_eq_sub_base (f := f) hInt a b
  have hF0 : F 0 = 0 := by simp [F]
  refine ⟨?hEquiv, ?hUnique, ?hSymm⟩
  · constructor
    · intro hR
      rcases hR with ⟨g, l, hg, hglim⟩
      let Lplus : ℝ := g 0
      have hTop : Tendsto F atTop (nhds Lplus) := by
        simpa [F, Lplus] using hg 0
      have hg_eq : ∀ a, g a = Lplus - F a := by
        intro a
        have h1 : Tendsto (fun b => F b - F a) atTop (nhds (g a)) := by
          simpa [hEqInt] using hg a
        have h2 : Tendsto (fun b => F b - F a) atTop (nhds (Lplus - F a)) :=
          hTop.sub tendsto_const_nhds
        exact tendsto_nhds_unique h1 h2
      have hglim' : Tendsto (fun a => Lplus - F a) atBot (nhds l) := by
        have hEq : (fun a => g a) = fun a => Lplus - F a := by
          funext a
          exact hg_eq a
        simpa [hEq] using hglim
      let Lminus : ℝ := Lplus - l
      have hbot : Tendsto F atBot (nhds Lminus) := by
        have hconst : Tendsto (fun _ : ℝ => Lplus) atBot (nhds Lplus) := tendsto_const_nhds
        have h := (hconst.sub hglim')
        have hfun : (fun a => Lplus - (Lplus - F a)) = fun a => F a := by
          funext a
          ring
        simpa [Lminus, hfun] using h
      let h : ℝ → ℝ := fun b => F b - Lminus
      have hhlim : ∀ b, Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b)) := by
        intro b
        have htemp :=
          tendsto_intervalIntegral_atBot_of_base (f := f) hInt (b := b) hbot
        simpa [h, F, Lminus] using htemp
      have hhtend : Tendsto h atTop (nhds l) := by
        have htemp : Tendsto (fun b => F b - Lminus) atTop (nhds (Lplus - Lminus)) :=
          hTop.sub tendsto_const_nhds
        have hval : Lplus - Lminus = l := by
          simp [Lminus]
        simpa [h, hval] using htemp
      exact ⟨h, l, hhlim, hhtend⟩
    · intro hL
      rcases hL with ⟨h, l, hh, hhtend⟩
      have hh0 : Tendsto (fun a : ℝ => ∫ x in a..(0 : ℝ), f x) atBot (nhds (h 0)) := hh 0
      have hh0' : Tendsto (fun a : ℝ => -F a) atBot (nhds (h 0)) := by
        simpa [hEqInt, hF0] using hh0
      let Lminus : ℝ := -h 0
      have hbot : Tendsto F atBot (nhds Lminus) := by
        have hconst :
            Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (nhds (0 : ℝ)) := tendsto_const_nhds
        have h := (hconst.sub hh0')
        have hfun : (fun a => (0 : ℝ) - (-F a)) = fun a => F a := by
          funext a
          ring
        simpa [Lminus, hfun] using h
      have hh_eq : ∀ b, h b = F b - Lminus := by
        intro b
        have h1 : Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b)) := hh b
        have h2 :
            Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (F b - Lminus)) := by
          have h2' :=
            tendsto_intervalIntegral_atBot_of_base (f := f) hInt (b := b) hbot
          simpa [F] using h2'
        exact tendsto_nhds_unique h1 h2
      have hhtend' : Tendsto (fun b => F b - Lminus) atTop (nhds l) := by
        have hEq : (fun b => h b) = fun b => F b - Lminus := by
          funext b
          exact hh_eq b
        simpa [hEq] using hhtend
      let Lplus : ℝ := Lminus + l
      have hTop : Tendsto F atTop (nhds Lplus) := by
        have hconst : Tendsto (fun _ : ℝ => Lminus) atTop (nhds Lminus) := tendsto_const_nhds
        have htemp := (hconst.add hhtend')
        have hfun : (fun b => Lminus + (F b - Lminus)) = fun b => F b := by
          funext b
          ring
        simpa [Lplus, hfun] using htemp
      let g : ℝ → ℝ := fun a => Lplus - F a
      have hg : ∀ a, Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds (g a)) := by
        intro a
        have htemp : Tendsto (fun b => F b - F a) atTop (nhds (Lplus - F a)) :=
          hTop.sub tendsto_const_nhds
        simpa [g, hEqInt] using htemp
      have hglim : Tendsto g atBot (nhds l) := by
        have hconst : Tendsto (fun _ : ℝ => Lplus) atBot (nhds Lplus) := tendsto_const_nhds
        have htemp : Tendsto (fun a => Lplus - F a) atBot (nhds (Lplus - Lminus)) :=
          hconst.sub hbot
        have hval : Lplus - Lminus = l := by
          simp [Lplus]
        simpa [g, hval] using htemp
      exact ⟨g, l, hg, hglim⟩
  · intro g h l₁ l₂ hg hglim hh hhtend
    let Lplus : ℝ := g 0
    have hTop : Tendsto F atTop (nhds Lplus) := by
      simpa [F, Lplus] using hg 0
    have hg_eq : ∀ a, g a = Lplus - F a := by
      intro a
      have h1 : Tendsto (fun b => F b - F a) atTop (nhds (g a)) := by
        simpa [hEqInt] using hg a
      have h2 : Tendsto (fun b => F b - F a) atTop (nhds (Lplus - F a)) :=
        hTop.sub tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    have hglim' : Tendsto (fun a => Lplus - F a) atBot (nhds l₁) := by
      have hEq : (fun a => g a) = fun a => Lplus - F a := by
        funext a
        exact hg_eq a
      simpa [hEq] using hglim
    let Lminus : ℝ := Lplus - l₁
    have hbot : Tendsto F atBot (nhds Lminus) := by
      have hconst : Tendsto (fun _ : ℝ => Lplus) atBot (nhds Lplus) := tendsto_const_nhds
      have h := (hconst.sub hglim')
      have hfun : (fun a => Lplus - (Lplus - F a)) = fun a => F a := by
        funext a
        ring
      simpa [Lminus, hfun] using h
    have hh_eq : ∀ b, h b = F b - Lminus := by
      intro b
      have h1 : Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b)) := hh b
      have h2 :
          Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (F b - Lminus)) := by
        have h2' :=
          tendsto_intervalIntegral_atBot_of_base (f := f) hInt (b := b) hbot
        simpa [F] using h2'
      exact tendsto_nhds_unique h1 h2
    have hhtend' : Tendsto (fun b => F b - Lminus) atTop (nhds l₂) := by
      have hEq : (fun b => h b) = fun b => F b - Lminus := by
        funext b
        exact hh_eq b
      simpa [hEq] using hhtend
    have hlimit : Tendsto (fun b => F b - Lminus) atTop (nhds (Lplus - Lminus)) :=
      hTop.sub tendsto_const_nhds
    have hl2 : l₂ = Lplus - Lminus := tendsto_nhds_unique hhtend' hlimit
    have hl1 : Lplus - Lminus = l₁ := by
      simp [Lminus]
    simpa [hl1] using hl2.symm
  · intro hR
    rcases hR with ⟨g, l, hg, hglim⟩
    let Lplus : ℝ := g 0
    have hTop : Tendsto F atTop (nhds Lplus) := by
      simpa [F, Lplus] using hg 0
    have hg_eq : ∀ a, g a = Lplus - F a := by
      intro a
      have h1 : Tendsto (fun b => F b - F a) atTop (nhds (g a)) := by
        simpa [hEqInt] using hg a
      have h2 : Tendsto (fun b => F b - F a) atTop (nhds (Lplus - F a)) :=
        hTop.sub tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    have hglim' : Tendsto (fun a => Lplus - F a) atBot (nhds l) := by
      have hEq : (fun a => g a) = fun a => Lplus - F a := by
        funext a
        exact hg_eq a
      simpa [hEq] using hglim
    let Lminus : ℝ := Lplus - l
    have hbot : Tendsto F atBot (nhds Lminus) := by
      have hconst : Tendsto (fun _ : ℝ => Lplus) atBot (nhds Lplus) := tendsto_const_nhds
      have h := (hconst.sub hglim')
      have hfun : (fun a => Lplus - (Lplus - F a)) = fun a => F a := by
        funext a
        ring
      simpa [Lminus, hfun] using h
    have hProd :
        Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (Filter.atBot ×ˢ Filter.atTop)
          (nhds (Lplus - Lminus)) :=
      tendsto_intervalIntegral_atBot_atTop_of_base (f := f) hInt hbot hTop
    have hval : Lplus - Lminus = l := by
      simp [Lminus]
    have hImp : ImproperIntegralRealLine f l := by
      refine ⟨hInt, ?_⟩
      simpa [hval] using hProd
    have hpair : Tendsto (fun a : ℝ => (-a, a)) atTop (Filter.atBot ×ˢ Filter.atTop) :=
      tendsto_neg_atTop_atBot.prodMk tendsto_id
    have hSymmTend :
        Tendsto (fun a : ℝ => ∫ x in (-a)..a, f x) atTop (nhds l) := by
      have hcomp := hProd.comp hpair
      simpa [hval] using hcomp
    exact ⟨l, hImp, hSymmTend⟩

/-- Example 5.5.11. For the function `f(x) = x / |x|` with `f(0) = 0`,
integrable on every bounded interval, the improper integral over the whole
line does not converge because for any fixed `a < 0` the limit
`lim_{b → ∞} ∫_{a}^{b} f` diverges. However, the symmetric partial integrals
`∫_{-a}^{a} f` are all zero for `a > 0`, so
`lim_{a → ∞} ∫_{-a}^{a} f = 0`. -/
theorem improperIntegral_sign_diverges_but_symmetric_zero :
    (∀ a : ℝ, a < 0 →
      ¬ ImproperIntegralAtTopConverges (fun x : ℝ => if x = 0 then 0 else x / |x|) a) ∧
      Tendsto (fun a : ℝ => ∫ x in (-a)..a, (if x = 0 then 0 else x / |x|)) atTop (nhds 0) :=
by
  classical
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else x / |x|
  have hEq_neg :
      ∀ {a : ℝ}, a < 0 →
        f =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a 0)] fun _ => (-1 : ℝ) := by
    intro a ha
    have hmem :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc a 0)), x ∈ (Set.uIoc a 0) := by
      simpa using
        (MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) (s := (Set.uIoc a 0))
          (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc (a : ℝ) 0))))
    have hne :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc a 0)), x ≠ (0 : ℝ) := by
      simpa using
        (MeasureTheory.Measure.ae_ne (MeasureTheory.volume.restrict (Set.uIoc a 0)) (0 : ℝ))
    refine (hmem.and hne).mono ?_
    intro x hx
    have hxmem : x ∈ Set.Ioc a 0 := by
      have hle : (a : ℝ) ≤ 0 := le_of_lt ha
      simpa [Set.uIoc_of_le hle] using hx.1
    have hxle : x ≤ 0 := hxmem.2
    have hxlt : x < 0 := lt_of_le_of_ne hxle hx.2
    have hxne : x ≠ 0 := hx.2
    calc
      f x = x / |x| := by simp [f, hxne]
      _ = x / (-x) := by simp [abs_of_neg hxlt]
      _ = -(x / x) := by simp [div_neg]
      _ = (-1 : ℝ) := by simp [hxne]
  have hEq_pos :
      ∀ {b : ℝ}, 0 < b → EqOn f (fun _ => (1 : ℝ)) (Set.uIoc 0 b) := by
    intro b hb x hx
    have hxmem : x ∈ Set.Ioc (0 : ℝ) b := by
      simpa [Set.uIoc_of_le (le_of_lt hb)] using hx
    have hxpos : 0 < x := hxmem.1
    calc
      f x = x / |x| := by simp [f, hxpos.ne']
      _ = x / x := by simp [abs_of_pos hxpos]
      _ = (1 : ℝ) := by simp [hxpos.ne']
  have hInt_a0 : ∀ {a : ℝ}, a < 0 → (∫ x in a..0, f x) = a := by
    intro a ha
    have hEq := hEq_neg (a := a) ha
    have hInt :
        ∫ x in a..0, f x = ∫ x in a..0, (-1 : ℝ) := by
      simpa using
        (intervalIntegral.integral_congr_ae_restrict (a := a) (b := 0)
          (μ := MeasureTheory.volume) hEq)
    calc
      ∫ x in a..0, f x = ∫ x in a..0, (-1 : ℝ) := hInt
      _ = (0 - a) * (-1 : ℝ) := by simp
      _ = a := by ring
  have hInt_0b : ∀ {b : ℝ}, 0 < b → (∫ x in 0..b, f x) = b := by
    intro b hb
    have hEq := hEq_pos (b := b) hb
    have hInt :
        ∫ x in 0..b, f x = ∫ x in 0..b, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact hEq hx
    calc
      ∫ x in 0..b, f x = ∫ x in 0..b, (1 : ℝ) := hInt
      _ = b := by simp
  have hInt_a0_int : ∀ {a : ℝ}, a < 0 → IntervalIntegrable f MeasureTheory.volume a 0 := by
    intro a ha
    have hEq := hEq_neg (a := a) ha
    have hconst :
        IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) MeasureTheory.volume a 0 :=
      intervalIntegrable_const
    exact (intervalIntegrable_congr_ae (f := f) (g := fun _ : ℝ => (-1 : ℝ)) hEq).2 hconst
  have hInt_0b_int : ∀ {b : ℝ}, 0 < b → IntervalIntegrable f MeasureTheory.volume 0 b := by
    intro b hb
    have hEq := hEq_pos (b := b) hb
    have hconst :
        IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 b :=
      intervalIntegrable_const
    exact (intervalIntegrable_congr (f := f) (g := fun _ : ℝ => (1 : ℝ)) hEq).2 hconst
  have hlim : ∀ {a : ℝ}, a < 0 →
      Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop atTop := by
    intro a ha
    have hEq :
        (fun b : ℝ => ∫ x in a..b, f x) =ᶠ[atTop] fun b => b + a := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
      intro b hb
      have hsplit :=
        intervalIntegral.integral_add_adjacent_intervals
          (hInt_a0_int (a := a) ha) (hInt_0b_int (b := b) hb)
      calc
        ∫ x in a..b, f x = (∫ x in a..0, f x) + ∫ x in 0..b, f x := hsplit.symm
        _ = a + b := by
          simp [hInt_a0 (a := a) ha, hInt_0b (b := b) hb]
        _ = b + a := by ac_rfl
    have hTend : Tendsto (fun b : ℝ => b + a) atTop atTop := tendsto_add_const_atTop a
    exact hTend.congr' hEq.symm
  refine ⟨?hdiv, ?hsymm⟩
  · intro a ha hconv
    rcases hconv with ⟨l, hl⟩
    have hTend := hlim (a := a) ha
    exact not_tendsto_nhds_of_tendsto_atTop hTend l (by simpa using hl.2)
  · have hEq :
        (fun a : ℝ => ∫ x in (-a)..a, f x) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
      intro a ha
      have ha' : 0 < a := by simpa using ha
      have hInt1 := hInt_a0 (a := -a) (by linarith [ha'])
      have hInt2 := hInt_0b (b := a) ha
      have hsplit :=
        intervalIntegral.integral_add_adjacent_intervals
          (hInt_a0_int (a := -a) (by linarith [ha'])) (hInt_0b_int (b := a) ha)
      calc
        ∫ x in (-a)..a, f x = (∫ x in (-a)..0, f x) + ∫ x in 0..a, f x := hsplit.symm
        _ = (-a) + a := by
          simp [hInt1, hInt2]
        _ = (0 : ℝ) := by ring
    have hTend : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds (0 : ℝ)) :=
      tendsto_const_nhds
    exact hTend.congr' hEq.symm

/-- Example 5.5.12. The sinc function is defined by
`sinc x = sin x / x` for `x ≠ 0` and `sinc 0 = 1`. Its improper integral over
the whole real line converges to `π`, while the improper integral of its
absolute value diverges. -/
noncomputable def sinc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

/-- Example 5.5.12. The improper integral of the sinc function over the real
line converges and equals `π`, but the integral of its absolute value diverges,
so the convergence is not absolute. -/
axiom improperIntegral_sinc_conditional :
    ImproperIntegralRealLine _root_.sinc Real.pi ∧
      ¬ ∃ l : ℝ, ImproperIntegralRealLine (fun x : ℝ => |_root_.sinc x|) l

/-- Proposition 5.5.13 (integral test for series). If `f : [k, ∞) → ℝ` is
nonnegative and decreasing for some integer `k`, then the series
`∑_{n = k}^{∞} f n` converges if and only if the improper integral `∫ k^∞ f`
converges. In the convergent case,
`∫ k^∞ f ≤ ∑_{n = k}^{∞} f n ≤ f k + ∫ k^∞ f`. -/
axiom integral_test_for_series {f : ℝ → ℝ} {k : ℕ}
    (hmono : AntitoneOn f (Set.Ici (k : ℝ)))
    (hpos : ∀ x, (k : ℝ) ≤ x → 0 ≤ f x)
    (hInt : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc (k : ℝ) c)) :
    (Summable (fun n : ℕ => f (n + k)) ↔ ImproperIntegralAtTopConverges f k) ∧
      (∀ {l}, ImproperIntegralAtTop f k l →
        Summable (fun n : ℕ => f (n + k)) →
          l ≤ tsum (fun n : ℕ => f (n + k)) ∧
            tsum (fun n : ℕ => f (n + k)) ≤ f k + l)

/-- Telescoping sum for successive differences. -/
lemma sum_range_sub_telescope (u : ℕ → ℝ) :
    ∀ N, (Finset.sum (Finset.range N) fun n => u n - u (n + 1)) = u 0 - u N := by
  intro N
  induction N with
  | zero =>
      simp
  | succ N ih =>
      calc
        Finset.sum (Finset.range N.succ) (fun n => u n - u (n + 1))
            = Finset.sum (Finset.range N) (fun n => u n - u (n + 1)) +
                (u N - u (N + 1)) := by
              simpa using
                (Finset.sum_range_succ (f := fun n => u n - u (n + 1)) N)
        _ = (u 0 - u N) + (u N - u (N + 1)) := by simp [ih]
        _ = u 0 - u (N + 1) := by ring

/-- For `m ≥ 1`, the term `1 / m^2` dominates the telescoping difference
`1 / m - 1 / (m + 1)`. -/
lemma inv_sq_ge_sub_inv_succ {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m : ℝ) ^ 2 ≥ 1 / (m : ℝ) - 1 / (m.succ : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hdiff :
      1 / (m : ℝ) - 1 / (m.succ : ℝ) =
        1 / ((m : ℝ) * (m.succ : ℝ)) := by
    have hmsucc : (m.succ : ℝ) = (m : ℝ) + 1 := by norm_cast
    have hcalc :
        1 / (m : ℝ) - 1 / ((m : ℝ) + 1) =
          1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
      have hpos : (m : ℝ) + 1 ≠ 0 := by nlinarith
      field_simp [hm0', hpos]
      ring_nf
    simpa [hmsucc] using hcalc
  have hmul_le : (m : ℝ) ^ 2 ≤ (m : ℝ) * (m.succ : ℝ) := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hm_le : (m : ℝ) ≤ m.succ := by exact_mod_cast (Nat.le_succ m)
    nlinarith
  have hpos : 0 < (m : ℝ) ^ 2 := pow_pos hm0 _
  have hrecip :
      1 / ((m : ℝ) * (m.succ : ℝ)) ≤ 1 / (m : ℝ) ^ 2 :=
    one_div_le_one_div_of_le hpos hmul_le
  calc
    1 / (m : ℝ) - 1 / (m.succ : ℝ)
        = 1 / ((m : ℝ) * (m.succ : ℝ)) := hdiff
    _ ≤ 1 / (m : ℝ) ^ 2 := hrecip

/-- For `m ≥ 1`, the next term `1 / (m + 1)^2` is bounded above by the same
telescoping difference `1 / m - 1 / (m + 1)`. -/
lemma inv_sq_succ_le_sub_inv {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m.succ : ℝ) ^ 2 ≤ 1 / (m : ℝ) - 1 / (m.succ : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hmpos_succ : 0 < (m.succ : ℝ) := by exact_mod_cast (Nat.succ_pos m)
  have hdiff :
      1 / (m : ℝ) - 1 / (m.succ : ℝ) =
        1 / ((m : ℝ) * (m.succ : ℝ)) := by
    have hmsucc : (m.succ : ℝ) = (m : ℝ) + 1 := by norm_cast
    have hcalc :
        1 / (m : ℝ) - 1 / ((m : ℝ) + 1) =
          1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
      have hpos : (m : ℝ) + 1 ≠ 0 := by nlinarith
      field_simp [hm0', hpos]
      ring_nf
    simpa [hmsucc] using hcalc
  have hmul_le : (m : ℝ) * (m.succ : ℝ) ≤ (m.succ : ℝ) ^ 2 := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hm_le : (m : ℝ) ≤ m.succ := by exact_mod_cast (Nat.le_succ m)
    nlinarith
  have hpos : 0 < (m : ℝ) * (m.succ : ℝ) := by
    nlinarith [hm0, hmpos_succ]
  have hrecip :
      1 / (m.succ : ℝ) ^ 2 ≤ 1 / ((m : ℝ) * (m.succ : ℝ)) :=
    one_div_le_one_div_of_le hpos hmul_le
  calc
    (1 : ℝ) / (m.succ : ℝ) ^ 2
        ≤ 1 / ((m : ℝ) * (m.succ : ℝ)) := hrecip
    _ = 1 / (m : ℝ) - 1 / (m.succ : ℝ) := hdiff.symm

set_option maxHeartbeats 10000000 in
-- The following summation estimate needs extra heartbeats.
lemma tail_bounds_one_div_nat_sq {k : ℕ} (hk : 1 ≤ k) :
    1 / (k : ℝ) ≤ tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) ∧
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) ≤
        1 / (k : ℝ) ^ 2 + 1 / (k : ℝ) := by
  classical
  have hbase :
      Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) :=
    (Real.summable_one_div_nat_pow).2 (by decide)
  have hs :
      Summable (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 hbase
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have htail_sum :
      Summable (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff k).2 hbase
  let u : ℕ → ℝ := fun n => (1 : ℝ) / ((n + k : ℕ) : ℝ)
  let g : ℕ → ℝ := fun n => u n - u (n + 1)
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    have hkpos : 0 < k := Nat.succ_le_iff.mp hk
    have hpos_nat : 0 < n + k := Nat.add_pos_right n hkpos
    have hpos : 0 < (n + k : ℝ) := by exact_mod_cast hpos_nat
    have hle : u (n + 1) ≤ u n := by
      have hle' : (n + k : ℝ) ≤ (n + k + 1 : ℝ) := by nlinarith
      have := one_div_le_one_div_of_le hpos hle'
      simpa [u, Nat.cast_add, Nat.cast_one, add_assoc, add_comm] using this
    exact sub_nonneg.mpr hle
  have hu : Tendsto u atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa [u, Nat.cast_add, Nat.cast_one] using
      ((tendsto_add_atTop_iff_nat k).2 h0)
  have hsum_g : HasSum g (1 / (k : ℝ)) := by
    have htel := sum_range_sub_telescope u
    have hlim :
        Tendsto (fun n => u 0 - u n) atTop (nhds ((u 0) - 0)) :=
      (tendsto_const_nhds.sub hu)
    have hpartial :
        Tendsto (fun n : ℕ => Finset.sum (Finset.range n) (fun i => g i))
          atTop (nhds (u 0)) := by
      simpa [g, htel] using hlim
    have hnonneg : ∀ i, 0 ≤ g i := hg_nonneg
    have hhas :=
      (hasSum_iff_tendsto_nat_of_nonneg hnonneg (u 0)).2 hpartial
    simpa [u, Nat.cast_add, Nat.cast_one] using hhas
  have tsum_g : tsum g = 1 / (k : ℝ) := hsum_g.tsum_eq
  have htail_lower :
      1 / (k : ℝ) ≤
        tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) := by
    have hle :
        ∀ n, g n ≤ (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) n := by
      intro n
      have hk'' : 1 ≤ n + k := by
        have h1 : 1 ≤ n + 1 := by exact Nat.succ_le_succ (Nat.zero_le n)
        exact le_trans h1 (Nat.add_le_add_left hk n)
      have := inv_sq_ge_sub_inv_succ (m := n + k) (by exact hk'')
      simpa [g, u, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    have := Summable.tsum_le_tsum (h := hle) hsum_g.summable htail_sum
    simpa [tsum_g] using this
  have htail_split :
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) =
        (1 : ℝ) / (k : ℝ) ^ 2 +
          tsum (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) :=
    by
      have := htail_sum.tsum_eq_zero_add
      simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm,
        add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have htail_succ_sum :
      Summable (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff k.succ).2 hbase
  have hupper_comp :
      ∀ n,
        (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) n ≤ g n := by
    intro n
    have hk'' : 1 ≤ n + k := by
      have h1 : 1 ≤ n + 1 := by exact Nat.succ_le_succ (Nat.zero_le n)
      exact le_trans h1 (Nat.add_le_add_left hk n)
    have := inv_sq_succ_le_sub_inv (m := n + k) hk''
    simpa [g, u, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have htail_succ_le : tsum (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) ≤
      tsum g :=
    Summable.tsum_le_tsum (h := hupper_comp) htail_succ_sum hsum_g.summable
  have htail_upper :
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) ≤
        1 / (k : ℝ) ^ 2 + 1 / (k : ℝ) := by
    calc
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2)
          = (1 : ℝ) / (k : ℝ) ^ 2 +
              tsum (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) :=
            htail_split
      _ ≤ (1 : ℝ) / (k : ℝ) ^ 2 + tsum g := by
            have := htail_succ_le
            linarith
      _ = 1 / (k : ℝ) ^ 2 + 1 / (k : ℝ) := by
            simp [tsum_g, add_comm]
  exact ⟨htail_lower, htail_upper⟩

/-- Example 5.5.14. Using the integral test with `f x = 1 / x^2` gives explicit
bounds on the Basel series. For any integer `k ≥ 1`,
`∑_{n=1}^{k-1} 1 / n^2 + 1 / k ≤ ∑_{n=1}^{∞} 1 / n^2 ≤
∑_{n=1}^{k-1} 1 / n^2 + 1 / k + 1 / k^2`. Numerically, taking `k = 10`
shows the sum lies between `1.6397…` and `1.6497…`, while the exact value is
`π^2 / 6 ≈ 1.6449…`. -/
theorem series_one_div_nat_sq_bounds {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) ∧
      ((Finset.sum (Finset.range (k - 1))
            (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) + 1 / (k : ℝ) ≤
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2)) ∧
      (tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) ≤
        Finset.sum (Finset.range (k - 1))
    (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) + 1 / (k : ℝ) +
          1 / ((k : ℝ) ^ 2))) :=
by
  classical
  -- Basic summability of the p-series with `p = 2`.
  have hbase :
      Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) :=
    (Real.summable_one_div_nat_pow).2 (by decide)
  have hs :
      Summable (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 hbase
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  -- Splitting the full sum into the first `k - 1` terms and the tail.
  have hsplit :
      Finset.sum (Finset.range (k - 1))
            (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
          tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) =
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) := by
    simpa [hk', Nat.succ_eq_add_one, Nat.add_assoc] using
      (Summable.sum_add_tsum_nat_add (k := k - 1) hs)
  have htsum_comm :
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) +
        Finset.sum (Finset.range (k - 1))
          (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) =
      tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) := by
    calc
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) +
            Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2)
          =
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) := by
        ac_rfl
      _ = tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) := hsplit
  have htail := tail_bounds_one_div_nat_sq hk
  -- Assemble the bounds.
  constructor
  · exact hs
  constructor
  · -- Lower bound with the partial sum.
    have hineq :=
      add_le_add_left htail.1
        (Finset.sum (Finset.range (k - 1))
          (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2))
    have hsum_le :
        Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) + 1 / (k : ℝ) ≤
          tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) := by
      have hrewrite := hsplit
      linarith
    exact hsum_le
  · -- Upper bound with the partial sum.
    have htsum :
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) =
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) := by
      exact hsplit.symm
    have hbound :
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) ≤
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            (1 / (k : ℝ) ^ 2 + 1 / (k : ℝ)) := by
      calc
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2)
            = Finset.sum (Finset.range (k - 1))
                  (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
                tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) := htsum
        _ ≤ Finset.sum (Finset.range (k - 1))
                (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
              (1 / (k : ℝ) ^ 2 + 1 / (k : ℝ)) := by
              linarith [htail.2]
    calc
      tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) ≤
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            (1 / (k : ℝ) ^ 2 + 1 / (k : ℝ)) := hbound
      _ =
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            1 / (k : ℝ) + 1 / (k : ℝ) ^ 2 := by
        ac_rfl

end Section05
end Chap05

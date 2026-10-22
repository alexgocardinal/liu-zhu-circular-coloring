import CircularColoring.CircularAttainment
import CircularColoring.Witness

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def IsIntegerCircularColoring
    {V : Type}
    (G : SimpleGraph V)
    (p q : Nat)
    (c : V → Nat) : Prop :=
  0 < q ∧
  2 * q ≤ p ∧
  (∀ v, c v < p) ∧
  (∀ u v, G.Adj u v →
    (q : ℤ) ≤ |(c u : ℤ) - (c v : ℤ)| ∧
      |(c u : ℤ) - (c v : ℤ)| ≤ (p - q : Nat))

theorem integerCircularColoring_to_real
    {V : Type}
    (G : SimpleGraph V)
    (p q : Nat)
    (c : V → Nat)
    (hc : IsIntegerCircularColoring G p q c) :
    IsRealCircularColoring G
      ((p : ℝ) / (q : ℝ))
      (fun v => (c v : ℝ) / (q : ℝ)) := by
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast hc.1
  have hpq : q ≤ p := by
    have h := hc.2.1
    omega
  have hpqReal : (q : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpq

  refine ⟨?_, ?_, ?_⟩
  · apply (le_div_iff₀ hq).2
    simpa using hpqReal

  · intro v
    change
      0 ≤ (c v : ℝ) / (q : ℝ) ∧
        (c v : ℝ) / (q : ℝ) ≤ (p : ℝ) / (q : ℝ)
    constructor
    · positivity
    · apply (div_le_div_iff_of_pos_right hq).2
      exact_mod_cast Nat.le_of_lt (hc.2.2.1 v)

  · intro u v huv
    have he := hc.2.2.2 u v huv

    have hlo :
        (q : ℝ) ≤ |(c u : ℝ) - (c v : ℝ)| := by
      exact_mod_cast he.1

    have hhiNat :
        |(c u : ℝ) - (c v : ℝ)| ≤ ((p - q : Nat) : ℝ) := by
      exact_mod_cast he.2

    have hhi :
        |(c u : ℝ) - (c v : ℝ)| ≤ (p : ℝ) - (q : ℝ) := by
      rw [Nat.cast_sub hpq] at hhiNat
      exact hhiNat

    change
      1 ≤ |(c u : ℝ) / (q : ℝ) - (c v : ℝ) / (q : ℝ)| ∧
        |(c u : ℝ) / (q : ℝ) - (c v : ℝ) / (q : ℝ)| ≤
          (p : ℝ) / (q : ℝ) - 1

    rw [← sub_div, abs_div, abs_of_pos hq]
    constructor
    · apply (le_div_iff₀ hq).2
      simpa using hlo
    · apply (div_le_iff₀ hq).2
      have hcancel :
          (p : ℝ) / (q : ℝ) * (q : ℝ) = (p : ℝ) :=
        div_mul_cancel₀ _ (ne_of_gt hq)
      nlinarith [hhi]

theorem integerCircularColoring_gives_real
    {V : Type}
    (G : SimpleGraph V)
    (p q : Nat)
    (c : V → Nat)
    (hc : IsIntegerCircularColoring G p q c) :
    HasRealCircularColoring G ((p : ℝ) / (q : ℝ)) :=
  ⟨fun v => (c v : ℝ) / (q : ℝ),
    integerCircularColoring_to_real G p q c hc⟩

theorem first_factor_integer_certificate :
    IsIntegerCircularColoring
      (circularComplete 5 2) 5 2 (fun v => v.val) := by
  unfold IsIntegerCircularColoring circularComplete
  decide

theorem second_factor_integer_certificate :
    IsIntegerCircularColoring
      (circularComplete 11 4) 11 4 (fun v => v.val) := by
  unfold IsIntegerCircularColoring circularComplete
  decide

theorem witness_integer_certificate :
    IsIntegerCircularColoring
      counterexampleGraph 17 2 witness := by
  unfold IsIntegerCircularColoring
    counterexampleGraph cartesianSumGraph circularComplete
  decide

theorem first_factor_real_colorable :
    HasRealCircularColoring
      (circularComplete 5 2) ((5 : ℝ) / 2) := by
  simpa using integerCircularColoring_gives_real
    (circularComplete 5 2) 5 2 (fun v => v.val)
    first_factor_integer_certificate

theorem second_factor_real_colorable :
    HasRealCircularColoring
      (circularComplete 11 4) ((11 : ℝ) / 4) := by
  simpa using integerCircularColoring_gives_real
    (circularComplete 11 4) 11 4 (fun v => v.val)
    second_factor_integer_certificate

theorem counterexample_real_colorable :
    HasRealCircularColoring
      counterexampleGraph ((17 : ℝ) / 2) := by
  simpa using integerCircularColoring_gives_real
    counterexampleGraph 17 2 witness witness_integer_certificate

theorem first_factor_circular_upper :
    realCircularChromaticNumber (circularComplete 5 2) ≤
      (5 : ℝ) / 2 :=
  realCircularChromaticNumber_le _ _ first_factor_real_colorable

theorem second_factor_circular_upper :
    realCircularChromaticNumber (circularComplete 11 4) ≤
      (11 : ℝ) / 4 :=
  realCircularChromaticNumber_le _ _ second_factor_real_colorable

theorem counterexample_circular_bounds :
    (33 : ℝ) / 4 < realCircularChromaticNumber counterexampleGraph ∧
      realCircularChromaticNumber counterexampleGraph ≤ (17 : ℝ) / 2 := by
  exact ⟨
    counterexample_strict_lower_bound _ counterexample_real_colorable,
    realCircularChromaticNumber_le _ _ counterexample_real_colorable⟩

end CircularColoring

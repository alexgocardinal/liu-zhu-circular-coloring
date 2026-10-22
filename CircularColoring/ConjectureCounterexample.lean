import CircularColoring.RealColoringCertificates

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def firstFactorThreeColor (v : Fin 5) : Fin 3 :=
  ⟨v.val / 2, by
    have h := v.isLt
    omega⟩

def secondFactorThreeColor (v : Fin 11) : Fin 3 :=
  ⟨v.val / 4, by
    have h := v.isLt
    omega⟩

theorem firstFactorThreeColor_proper :
    ∀ u v : Fin 5,
      2 ≤ circularDistance 5 u.val v.val →
      firstFactorThreeColor u ≠ firstFactorThreeColor v := by
  decide

theorem secondFactorThreeColor_proper :
    ∀ u v : Fin 11,
      4 ≤ circularDistance 11 u.val v.val →
      secondFactorThreeColor u ≠ secondFactorThreeColor v := by
  decide

def firstFactorThreeColoring :
    (circularComplete 5 2).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk firstFactorThreeColor (by
    intro u v huv
    exact firstFactorThreeColor_proper u v huv.2)

def secondFactorThreeColoring :
    (circularComplete 11 4).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk secondFactorThreeColor (by
    intro u v huv
    exact secondFactorThreeColor_proper u v huv.2)

theorem first_factor_ordinary_upper :
    (circularComplete 5 2).chromaticNumber.toNat ≤ 3 := by
  have hcolorable : (circularComplete 5 2).Colorable 3 :=
    ⟨firstFactorThreeColoring⟩
  exact ENat.toNat_le_of_le_natCast hcolorable.chromaticNumber_le

theorem second_factor_ordinary_upper :
    (circularComplete 11 4).chromaticNumber.toNat ≤ 3 := by
  have hcolorable : (circularComplete 11 4).Colorable 3 :=
    ⟨secondFactorThreeColoring⟩
  exact ENat.toNat_le_of_le_natCast hcolorable.chromaticNumber_le

theorem conjectured_bound_le_thirty_three_quarters :
    max
      (realCircularChromaticNumber (circularComplete 5 2) *
        ((circularComplete 11 4).chromaticNumber.toNat : ℝ))
      (((circularComplete 5 2).chromaticNumber.toNat : ℝ) *
        realCircularChromaticNumber (circularComplete 11 4)) ≤
      (33 : ℝ) / 4 := by
  have hfirst :
      ((circularComplete 5 2).chromaticNumber.toNat : ℝ) ≤ 3 := by
    exact_mod_cast first_factor_ordinary_upper
  have hsecond :
      ((circularComplete 11 4).chromaticNumber.toNat : ℝ) ≤ 3 := by
    exact_mod_cast second_factor_ordinary_upper
  have hfirst0 :
      0 ≤ ((circularComplete 5 2).chromaticNumber.toNat : ℝ) := by
    positivity
  have hsecond0 :
      0 ≤ ((circularComplete 11 4).chromaticNumber.toNat : ℝ) := by
    positivity

  apply max_le
  · calc
      realCircularChromaticNumber (circularComplete 5 2) *
          ((circularComplete 11 4).chromaticNumber.toNat : ℝ) ≤
        ((5 : ℝ) / 2) *
          ((circularComplete 11 4).chromaticNumber.toNat : ℝ) :=
        mul_le_mul_of_nonneg_right first_factor_circular_upper hsecond0
      _ ≤ ((5 : ℝ) / 2) * 3 :=
        mul_le_mul_of_nonneg_left hsecond (by norm_num)
      _ ≤ (33 : ℝ) / 4 := by norm_num
  · calc
      ((circularComplete 5 2).chromaticNumber.toNat : ℝ) *
          realCircularChromaticNumber (circularComplete 11 4) ≤
        ((circularComplete 5 2).chromaticNumber.toNat : ℝ) *
          ((11 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left second_factor_circular_upper hfirst0
      _ ≤ 3 * ((11 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hfirst (by norm_num)
      _ = (33 : ℝ) / 4 := by norm_num

-- The actual proposed bound is strictly below the product's
-- circular chromatic number.
theorem liu_zhu_strict_counterexample :
    max
      (realCircularChromaticNumber (circularComplete 5 2) *
        ((circularComplete 11 4).chromaticNumber.toNat : ℝ))
      (((circularComplete 5 2).chromaticNumber.toNat : ℝ) *
        realCircularChromaticNumber (circularComplete 11 4)) <
      realCircularChromaticNumber counterexampleGraph := by
  exact lt_of_le_of_lt
    conjectured_bound_le_thirty_three_quarters
    counterexample_circular_bounds.1

theorem liu_zhu_counterexample :
    ¬ LiuZhuInequality
      (circularComplete 5 2) (circularComplete 11 4) := by
  intro h
  exact (not_le_of_gt liu_zhu_strict_counterexample) h

end CircularColoring

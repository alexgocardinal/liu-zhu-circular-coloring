import CircularColoring.RealCircularColoring

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- Multiply a real color by four and take its integer floor.
-- The temporary range includes 33, which will wrap back to zero.
noncomputable def floorSlot34
    (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (33 : ℝ) / 4) : Fin 34 :=
  ⟨(⌊4 * x⌋ : ℤ).toNat, by
    have hnonneg : 0 ≤ (⌊4 * x⌋ : ℤ) :=
      Int.floor_nonneg.mpr (by linarith [hx.1])
    have hreal : ((⌊4 * x⌋ : ℤ) : ℝ) ≤ 33 := by
      have hf := Int.floor_le (4 * x)
      linarith [hx.2]
    have hint : (⌊4 * x⌋ : ℤ) ≤ 33 := by
      exact_mod_cast hreal
    omega⟩

noncomputable def roundedColor33
    (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (33 : ℝ) / 4) : Fin 33 :=
  ⟨(floorSlot34 x hx).val % 33, Nat.mod_lt _ (by decide)⟩

theorem floorSlot34_bounds
    (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (33 : ℝ) / 4) :
    ((floorSlot34 x hx).val : ℝ) ≤ 4 * x ∧
      4 * x < ((floorSlot34 x hx).val : ℝ) + 1 := by
  have hnonneg : 0 ≤ (⌊4 * x⌋ : ℤ) :=
    Int.floor_nonneg.mpr (by linarith [hx.1])
  have hint :
      ((floorSlot34 x hx).val : ℤ) = (⌊4 * x⌋ : ℤ) := by
    change (((⌊4 * x⌋ : ℤ).toNat : Nat) : ℤ) =
      (⌊4 * x⌋ : ℤ)
    omega
  have hreal :
      ((floorSlot34 x hx).val : ℝ) =
        ((⌊4 * x⌋ : ℤ) : ℝ) := by
    exact_mod_cast hint
  rw [hreal]
  exact ⟨Int.floor_le (4 * x), Int.lt_floor_add_one (4 * x)⟩

theorem floorSlot34_ordered_gap
    (x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (33 : ℝ) / 4)
    (hy : 0 ≤ y ∧ y ≤ (33 : ℝ) / 4)
    (hlower : 1 ≤ y - x)
    (hupper : y - x ≤ (29 : ℝ) / 4) :
    (4 : ℤ) ≤
        (floorSlot34 y hy).val - (floorSlot34 x hx).val ∧
      (floorSlot34 y hy).val - (floorSlot34 x hx).val ≤
        (29 : ℤ) := by
  have hfx := floorSlot34_bounds x hx
  have hfy := floorSlot34_bounds y hy
  have hlo :
      (3 : ℝ) <
        ((floorSlot34 y hy).val : ℝ) -
          ((floorSlot34 x hx).val : ℝ) := by
    linarith [hfx.1, hfy.2]
  have hhi :
      ((floorSlot34 y hy).val : ℝ) -
        ((floorSlot34 x hx).val : ℝ) < 30 := by
    linarith [hfx.2, hfy.1]
  have hloInt :
      (3 : ℤ) <
        (floorSlot34 y hy).val - (floorSlot34 x hx).val := by
    exact_mod_cast hlo
  have hhiInt :
      (floorSlot34 y hy).val - (floorSlot34 x hx).val <
        (30 : ℤ) := by
    exact_mod_cast hhi
  omega

-- Check the finite wraparound calculation, including the endpoint 33.
theorem rounded_slots_finite_check :
    ∀ a b : Fin 34,
      (4 : ℤ) ≤ |(a.val : ℤ) - (b.val : ℤ)| →
      |(a.val : ℤ) - (b.val : ℤ)| ≤ 29 →
      4 ≤ circularDistance 33 (a.val % 33) (b.val % 33) := by
  decide

theorem rounding_preserves_ordered_separation
    (x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (33 : ℝ) / 4)
    (hy : 0 ≤ y ∧ y ≤ (33 : ℝ) / 4)
    (hlower : 1 ≤ y - x)
    (hupper : y - x ≤ (29 : ℝ) / 4) :
    4 ≤ circularDistance 33
      (roundedColor33 x hx).val (roundedColor33 y hy).val := by
  have hgap := floorSlot34_ordered_gap x y hx hy hlower hupper
  have hsign :
      (floorSlot34 x hx).val - (floorSlot34 y hy).val ≤
        (0 : ℤ) := by
    omega
  have habs :
      |((floorSlot34 x hx).val : ℤ) -
        ((floorSlot34 y hy).val : ℤ)| =
      ((floorSlot34 y hy).val : ℤ) -
        ((floorSlot34 x hx).val : ℤ) := by
    rw [abs_of_nonpos hsign]
    ring
  exact rounded_slots_finite_check
    (floorSlot34 x hx) (floorSlot34 y hy)
    (by rw [habs]; exact hgap.1)
    (by rw [habs]; exact hgap.2)

theorem rounding_preserves_separation
    (x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (33 : ℝ) / 4)
    (hy : 0 ≤ y ∧ y ≤ (33 : ℝ) / 4)
    (hsep : 1 ≤ |x - y| ∧ |x - y| ≤ (29 : ℝ) / 4) :
    4 ≤ circularDistance 33
      (roundedColor33 x hx).val (roundedColor33 y hy).val := by
  by_cases hxy : x ≤ y
  · have hg : 1 ≤ y - x ∧ y - x ≤ (29 : ℝ) / 4 := by
      simpa only [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
        using hsep
    exact rounding_preserves_ordered_separation
      x y hx hy hg.1 hg.2
  · have hyx : y ≤ x := by linarith
    have hg : 1 ≤ x - y ∧ x - y ≤ (29 : ℝ) / 4 := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr hyx)] using hsep
    have h := rounding_preserves_ordered_separation
      y x hy hx hg.1 hg.2
    simpa only [circularDistance, Nat.min_comm] using h

theorem no_real_coloring33_4 :
    ¬ HasRealCircularColoring counterexampleGraph ((33 : ℝ) / 4) := by
  rintro ⟨c, hc⟩
  apply no_coloring33_4
  refine ⟨fun v => roundedColor33 (c v) (hc.2.1 v), ?_⟩
  intro u v huv
  have he := hc.2.2 u v
    ((counterexampleGraph_adjacency u v).mpr huv)
  have hsep :
      1 ≤ |c u - c v| ∧ |c u - c v| ≤ (29 : ℝ) / 4 := by
    refine ⟨he.1, ?_⟩
    linarith [he.2]
  exact rounding_preserves_separation
    (c u) (c v) (hc.2.1 u) (hc.2.1 v) hsep

end CircularColoring

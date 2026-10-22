import CircularColoring.ConjectureGraphs

namespace CircularColoring

-- Colors lie on a circle of circumference r.
-- Adjacent vertices have distance at least one in both directions.
def IsRealCircularColoring
    {V : Type}
    (G : SimpleGraph V)
    (r : ℝ)
    (c : V → ℝ) : Prop :=
  1 ≤ r ∧
  (∀ v, 0 ≤ c v ∧ c v ≤ r) ∧
  (∀ u v, G.Adj u v →
    1 ≤ |c u - c v| ∧ |c u - c v| ≤ r - 1)

def HasRealCircularColoring
    {V : Type}
    (G : SimpleGraph V)
    (r : ℝ) : Prop :=
  ∃ c : V → ℝ, IsRealCircularColoring G r c

def circularCircumferences
    {V : Type}
    (G : SimpleGraph V) : Set ℝ :=
  {r | HasRealCircularColoring G r}

-- We will prove the needed existence and attainment results before
-- using this infimum for the finite graphs in the counterexample.
noncomputable def realCircularChromaticNumber
    {V : Type}
    (G : SimpleGraph V) : ℝ :=
  sInf (circularCircumferences G)

theorem circularCircumferences_bddBelow
    {V : Type}
    (G : SimpleGraph V) :
    BddBelow (circularCircumferences G) := by
  refine ⟨1, ?_⟩
  intro r hr
  obtain ⟨c, hc⟩ := hr
  exact hc.1

theorem realCircularChromaticNumber_le
    {V : Type}
    (G : SimpleGraph V)
    (r : ℝ)
    (h : HasRealCircularColoring G r) :
    realCircularChromaticNumber G ≤ r := by
  exact csInf_le (circularCircumferences_bddBelow G) h

theorem one_le_realCircularChromaticNumber
    {V : Type}
    (G : SimpleGraph V)
    (hne : (circularCircumferences G).Nonempty) :
    1 ≤ realCircularChromaticNumber G := by
  apply le_csInf hne
  intro r hr
  obtain ⟨c, hc⟩ := hr
  exact hc.1

-- Increasing the circumference preserves a coloring.
theorem realCircularColoring_mono
    {V : Type}
    (G : SimpleGraph V)
    (r s : ℝ)
    (c : V → ℝ)
    (hc : IsRealCircularColoring G r c)
    (hrs : r ≤ s) :
    IsRealCircularColoring G s c := by
  refine ⟨le_trans hc.1 hrs, ?_, ?_⟩
  · intro v
    exact ⟨(hc.2.1 v).1, le_trans (hc.2.1 v).2 hrs⟩
  · intro u v huv
    have he := hc.2.2 u v huv
    refine ⟨he.1, ?_⟩
    linarith [he.2]

theorem hasRealCircularColoring_mono
    {V : Type}
    (G : SimpleGraph V)
    (r s : ℝ)
    (hr : HasRealCircularColoring G r)
    (hrs : r ≤ s) :
    HasRealCircularColoring G s := by
  obtain ⟨c, hc⟩ := hr
  exact ⟨c, realCircularColoring_mono G r s c hc hrs⟩

theorem realCircularColoring_edge_bound
    {V : Type}
    (G : SimpleGraph V)
    (r : ℝ)
    (c : V → ℝ)
    (hc : IsRealCircularColoring G r c)
    (u v : V)
    (huv : G.Adj u v) :
    2 ≤ r := by
  have he := hc.2.2 u v huv
  linarith [he.1, he.2]

-- The Liu–Zhu inequality for nonempty finite graphs.
def LiuZhuInequality
    {V W : Type}
    [Fintype V] [Fintype W]
    [Nonempty V] [Nonempty W]
    (G : SimpleGraph V)
    (H : SimpleGraph W) : Prop :=
  realCircularChromaticNumber (cartesianSumGraph G H) ≤
    max
      (realCircularChromaticNumber G *
        (H.chromaticNumber.toNat : ℝ))
      ((G.chromaticNumber.toNat : ℝ) *
        realCircularChromaticNumber H)

end CircularColoring

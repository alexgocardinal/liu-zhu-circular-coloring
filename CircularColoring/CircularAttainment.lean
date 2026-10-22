import CircularColoring.RoundingBridge

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- The coloring inequalities define a closed set.
theorem realColoringPairs_isClosed
    {V : Type}
    (G : SimpleGraph V) :
    IsClosed {z : ℝ × (V → ℝ) |
      IsRealCircularColoring G z.1 z.2} := by
  have hv (v : V) :
      Continuous (fun z : ℝ × (V → ℝ) => z.2 v) :=
    (continuous_apply v).comp continuous_snd

  have hd (u v : V) :
      Continuous (fun z : ℝ × (V → ℝ) => |z.2 u - z.2 v|) :=
    ((hv u).sub (hv v)).abs

  have hlow : IsClosed {z : ℝ × (V → ℝ) | 1 ≤ z.1} :=
    isClosed_le continuous_const continuous_fst

  have hb : IsClosed {z : ℝ × (V → ℝ) |
      ∀ v, 0 ≤ z.2 v ∧ z.2 v ≤ z.1} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    apply isClosed_iInter
    intro v
    exact
      (isClosed_le continuous_const (hv v)).inter
        (isClosed_le (hv v) continuous_fst)

  have he : IsClosed {z : ℝ × (V → ℝ) |
      ∀ u v, G.Adj u v →
        1 ≤ |z.2 u - z.2 v| ∧
          |z.2 u - z.2 v| ≤ z.1 - 1} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro _
    exact
      (isClosed_le continuous_const (hd u v)).inter
        (isClosed_le (hd u v) (continuous_fst.sub continuous_const))

  simpa only [IsRealCircularColoring, Set.ofPred_and]
    using hlow.inter (hb.inter he)

def boundedColoringPairs
    {V : Type}
    (G : SimpleGraph V)
    (R : ℝ) : Set (ℝ × (V → ℝ)) :=
  {z | IsRealCircularColoring G z.1 z.2 ∧ z.1 ≤ R}

-- All feasible colorings below a fixed circumference lie in a compact box.
theorem boundedColoringPairs_isCompact
    {V : Type}
    (G : SimpleGraph V)
    (R : ℝ) :
    IsCompact (boundedColoringPairs G R) := by
  have hbox :
      IsCompact
        ((Set.Icc (1 : ℝ) R) ×ˢ
          {c : V → ℝ | ∀ v, c v ∈ Set.Icc (0 : ℝ) R}) :=
    isCompact_Icc.prod
      (isCompact_pi_infinite (fun _ : V => isCompact_Icc))

  have hclosed : IsClosed (boundedColoringPairs G R) :=
    (realColoringPairs_isClosed G).inter
      (isClosed_le continuous_fst continuous_const)

  apply hbox.of_isClosed_subset hclosed
  intro z hz
  refine ⟨⟨hz.1.1, hz.2⟩, ?_⟩
  intro v
  exact ⟨(hz.1.2.1 v).1, le_trans (hz.1.2.1 v).2 hz.2⟩

theorem realCircularChromaticNumber_attained
    {V : Type}
    (G : SimpleGraph V)
    (R : ℝ)
    (hR : HasRealCircularColoring G R) :
    HasRealCircularColoring G (realCircularChromaticNumber G) := by
  obtain ⟨cR, hcR⟩ := hR

  have hnonempty : (boundedColoringPairs G R).Nonempty :=
    ⟨(R, cR), hcR, le_rfl⟩

  let S : Set ℝ := Prod.fst '' boundedColoringPairs G R

  have hcompact : IsCompact S :=
    (boundedColoringPairs_isCompact G R).image continuous_fst
  have hSnonempty : S.Nonempty :=
    hnonempty.image Prod.fst

  obtain ⟨r, hr⟩ := hcompact.exists_isLeast hSnonempty
  rcases hr.1 with ⟨z, hz, hzr⟩

  have hrcolor : HasRealCircularColoring G r := by
    refine ⟨z.2, ?_⟩
    rw [← hzr]
    exact hz.1

  have hrR : r ≤ R := by
    rw [← hzr]
    exact hz.2

  have hminimal : ∀ s ∈ circularCircumferences G, r ≤ s := by
    intro s hs
    by_cases hsR : s ≤ R
    · obtain ⟨c, hc⟩ := hs
      apply hr.2
      exact ⟨(s, c), ⟨hc, hsR⟩, rfl⟩
    · have hRs : R ≤ s := by linarith
      exact le_trans hrR hRs

  have hcircnonempty : (circularCircumferences G).Nonempty :=
    ⟨R, cR, hcR⟩

  have heq : realCircularChromaticNumber G = r :=
    le_antisymm
      (realCircularChromaticNumber_le G r hrcolor)
      (le_csInf hcircnonempty hminimal)

  rw [heq]
  exact hrcolor

-- Any known real coloring supplies the upper bound needed for attainment.
theorem counterexample_strict_lower_bound
    (R : ℝ)
    (hR : HasRealCircularColoring counterexampleGraph R) :
    (33 : ℝ) / 4 < realCircularChromaticNumber counterexampleGraph := by
  by_contra h
  have hle :
      realCircularChromaticNumber counterexampleGraph ≤
        (33 : ℝ) / 4 := by
    linarith
  have hmin :=
    realCircularChromaticNumber_attained counterexampleGraph R hR
  exact no_real_coloring33_4
    (hasRealCircularColoring_mono counterexampleGraph
      (realCircularChromaticNumber counterexampleGraph)
      ((33 : ℝ) / 4) hmin hle)

end CircularColoring

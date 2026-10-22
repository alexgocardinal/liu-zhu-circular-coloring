import CircularColoring.Saturation

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def secondArc (start : Fin 11) : Finset (Fin 11) :=
  Finset.univ.filter fun b =>
    (b.val + 11 - start.val) % 11 < 4

-- Classify all maximum independent sets of K_(11/4).
theorem maximum_independent_is_arc :
    ∀ s : Finset (Fin 11),
      s.card = 4 →
      (∀ b ∈ s, ∀ d ∈ s,
        circularDistance 11 b.val d.val < 4) →
      ∃! start : Fin 11, s = secondArc start := by
  unfold ExistsUnique
  decide

theorem activeFibers_independent
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    ∀ b ∈ activeFibers c t, ∀ d ∈ activeFibers c t,
      circularDistance 11 b.val d.val < 4 := by
  intro b hb d hd
  rcases (Finset.mem_filter.mp hb).2 with ⟨a, ha⟩
  rcases (Finset.mem_filter.mp hd).2 with ⟨a', ha'⟩
  by_contra hfar
  have hAdj : Adj (a, b) (a', d) :=
    Or.inr (Nat.le_of_not_gt hfar)
  have hdis :=
    colorIntervals_disjoint
      (c (a, b)) (c (a', d)) (hc _ _ hAdj)
  exact Finset.disjoint_left.mp hdis ha ha'

theorem activeFibers_is_arc
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    ∃! start : Fin 11, activeFibers c t = secondArc start := by
  exact maximum_independent_is_arc
    (activeFibers c t)
    (activeFibers_card_eq_four c hc t)
    (activeFibers_independent c hc t)

end CircularColoring

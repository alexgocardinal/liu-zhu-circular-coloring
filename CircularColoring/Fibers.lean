import CircularColoring.Intervals

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 0

-- The exact coloring whose existence we want to rule out.
def IsColoring33_4 (c : Vertex → Fin 33) : Prop :=
  ∀ u v : Vertex, Adj u v →
    4 ≤ circularDistance 33 (c u).val (c v).val

-- Independent sets in K_(11/4) have at most four vertices.
theorem second_coordinate_independent_bound :
    ∀ s : Finset (Fin 11),
      (∀ b ∈ s, ∀ d ∈ s,
        circularDistance 11 b.val d.val < 4) →
      s.card ≤ 4 := by
  decide

-- Which second coordinates occupy position t?
def activeFibers (c : Vertex → Fin 33) (t : Fin 33) :
    Finset (Fin 11) :=
  Finset.univ.filter fun b =>
    ∃ a : Fin 5, t ∈ colorInterval (c (a, b))

theorem activeFibers_card_le_four
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    (activeFibers c t).card ≤ 4 := by
  apply second_coordinate_independent_bound
  intro b hb d hd
  rcases (Finset.mem_filter.mp hb).2 with ⟨a, ha⟩
  rcases (Finset.mem_filter.mp hd).2 with ⟨a', ha'⟩
  by_contra hfar
  have hAdj : Adj (a, b) (a', d) := by
    right
    exact Nat.le_of_not_gt hfar
  have hdis :=
    colorIntervals_disjoint
      (c (a, b)) (c (a', d)) (hc _ _ hAdj)
  exact Finset.disjoint_left.mp hdis ha ha'

end CircularColoring

import CircularColoring.CyclicGrowth

namespace CircularColoring

open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def rowPositions
    (c : Vertex → Fin 33)
    (a : Fin 5) : Finset (Fin 33) :=
  Finset.univ.biUnion fun b : Fin 11 =>
    colorInterval (c (a, b))

def activeRows
    (c : Vertex → Fin 33)
    (t : Fin 33) : Finset (Fin 5) :=
  Finset.univ.filter fun a =>
    ∃ b : Fin 11, t ∈ colorInterval (c (a, b))

theorem mem_row_iff_active
    (c : Vertex → Fin 33)
    (a : Fin 5)
    (t : Fin 33) :
    t ∈ rowPositions c a ↔ a ∈ activeRows c t := by
  simp [rowPositions, activeRows]

theorem first_coordinate_independent_bound :
    ∀ s : Finset (Fin 5),
      (∀ a ∈ s, ∀ d ∈ s,
        circularDistance 5 a.val d.val < 2) →
      s.card ≤ 2 := by
  decide

theorem activeRows_card_le_two
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    (activeRows c t).card ≤ 2 := by
  apply first_coordinate_independent_bound
  intro a ha d hd
  rcases (Finset.mem_filter.mp ha).2 with ⟨b, hb⟩
  rcases (Finset.mem_filter.mp hd).2 with ⟨e, he⟩
  by_contra hfar
  have hAdj : Adj (a, b) (d, e) :=
    Or.inl (Nat.le_of_not_gt hfar)
  have hdis :=
    colorIntervals_disjoint
      (c (a, b)) (c (d, e)) (hc _ _ hAdj)
  exact Finset.disjoint_left.mp hdis hb he

theorem row_occupancy_double_count
    (c : Vertex → Fin 33) :
    (∑ a : Fin 5, (rowPositions c a).card) =
      ∑ t : Fin 33, (activeRows c t).card := by
  let r : Fin 5 → Fin 33 → Prop :=
    fun a t => t ∈ rowPositions c a

  have habove (a : Fin 5) :
      (Finset.univ : Finset (Fin 33)).bipartiteAbove r a =
        rowPositions c a := by
    ext t
    simp [Finset.bipartiteAbove, r]

  have hbelow (t : Fin 33) :
      (Finset.univ : Finset (Fin 5)).bipartiteBelow r t =
        activeRows c t := by
    ext a
    simp [Finset.bipartiteBelow, r, mem_row_iff_active]

  have hcount :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (Fin 5)))
      (t := (Finset.univ : Finset (Fin 33))) r

  simpa only [habove, hbelow] using hcount

theorem total_row_occupancy_le_sixty_six
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c) :
    (∑ a : Fin 5, (rowPositions c a).card) ≤ 66 := by
  rw [row_occupancy_double_count]
  calc
    (∑ t : Fin 33, (activeRows c t).card) ≤
        ∑ _t : Fin 33, (2 : Nat) := by
      apply Finset.sum_le_sum
      intro t _
      exact activeRows_card_le_two c hc t
    _ = 66 := by norm_num

end CircularColoring

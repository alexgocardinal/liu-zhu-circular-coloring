import CircularColoring.ActiveArcs

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem fiberPositions_eq_three_intervals
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11) :
    ∃ x y z : Fin 33,
      Disjoint (colorInterval x) (colorInterval y) ∧
      Disjoint (colorInterval x) (colorInterval z) ∧
      Disjoint (colorInterval y) (colorInterval z) ∧
      fiberPositions c b =
        (colorInterval x ∪ colorInterval y) ∪ colorInterval z := by
  obtain ⟨i, j, k, hij, hik, hjk⟩ :=
    three_separated_in_fiber c hc b

  let A := colorInterval (c (i, b))
  let B := colorInterval (c (j, b))
  let C := colorInterval (c (k, b))

  have hAB : Disjoint A B :=
    colorIntervals_disjoint _ _ hij
  have hAC : Disjoint A C :=
    colorIntervals_disjoint _ _ hik
  have hBC : Disjoint B C :=
    colorIntervals_disjoint _ _ hjk
  have hABC : Disjoint (A ∪ B) C :=
    Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩

  have hA : A.card = 4 := colorInterval_card _
  have hB : B.card = 4 := colorInterval_card _
  have hC : C.card = 4 := colorInterval_card _
  have hsize : ((A ∪ B) ∪ C).card = 12 := by
    rw [Finset.card_union_of_disjoint hABC,
      Finset.card_union_of_disjoint hAB, hA, hB, hC]

  have hsub : (A ∪ B) ∪ C ⊆ fiberPositions c b := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ i, ht⟩
      · exact Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_univ j, ht⟩
    · exact Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_univ k, ht⟩

  have hcard :
      (fiberPositions c b).card ≤ ((A ∪ B) ∪ C).card := by
    rw [fiberPositions_card_eq_twelve c hc b, hsize]

  have heq : (A ∪ B) ∪ C = fiberPositions c b :=
    Finset.eq_of_subset_of_card_le hsub hcard

  exact ⟨c (i, b), c (j, b), c (k, b),
    hAB, hAC, hBC, heq.symm⟩

end CircularColoring

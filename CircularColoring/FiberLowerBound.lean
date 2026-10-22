import CircularColoring.FiberGeometry

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem three_separated_in_fiber
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11) :
    ∃ i j k : Fin 5,
      4 ≤ circularDistance 33 (c (i, b)).val (c (j, b)).val ∧
      4 ≤ circularDistance 33 (c (i, b)).val (c (k, b)).val ∧
      4 ≤ circularDistance 33 (c (j, b)).val (c (k, b)).val := by
  let x : Fin 5 → Fin 33 := fun i => c (i, b)
  have h (i j : Fin 5)
      (hij : 2 ≤ circularDistance 5 i.val j.val) :
      4 ≤ circularDistance 33 (x i).val (x j).val :=
    hc (i, b) (j, b) (Or.inl hij)

  have h02 := h 0 2 (by decide)
  have h03 := h 0 3 (by decide)
  have h13 := h 1 3 (by decide)
  have h14 := h 1 4 (by decide)
  have h24 := h 2 4 (by decide)

  let y : Fin 5 → Fin 33 :=
    fun i => rotateColor (x i) (x 0)
  have hy0 : y 0 = 0 := rotateColor_self (x 0)
  have hrot (i j : Fin 5) :
      circularDistance 33 (y i).val (y j).val =
      circularDistance 33 (x i).val (x j).val :=
    rotation_preserves_distance (x i) (x j) (x 0)

  have hy (i j : Fin 5)
      (hij : 2 ≤ circularDistance 5 i.val j.val) :
      4 ≤ circularDistance 33 (y i).val (y j).val := by
    rw [hrot]
    exact h i j hij

  have he' := extra_separated_pair_at_zero
    (y 1) (y 2) (y 3) (y 4)
    (by simpa only [hy0, Fin.val_zero] using hy 0 2 (by decide))
    (by simpa only [hy0, Fin.val_zero] using hy 0 3 (by decide))
    (hy 1 3 (by decide))
    (hy 1 4 (by decide))
    (hy 2 4 (by decide))

  have heY :
      4 ≤ circularDistance 33 (y 0).val (y 1).val ∨
      4 ≤ circularDistance 33 (y 1).val (y 2).val ∨
      4 ≤ circularDistance 33 (y 2).val (y 3).val ∨
      4 ≤ circularDistance 33 (y 3).val (y 4).val ∨
      4 ≤ circularDistance 33 (y 4).val (y 0).val := by
    simpa only [hy0, Fin.val_zero] using he'

  have he :
      4 ≤ circularDistance 33 (x 0).val (x 1).val ∨
      4 ≤ circularDistance 33 (x 1).val (x 2).val ∨
      4 ≤ circularDistance 33 (x 2).val (x 3).val ∨
      4 ≤ circularDistance 33 (x 3).val (x 4).val ∨
      4 ≤ circularDistance 33 (x 4).val (x 0).val := by
    simpa only [hrot] using heY

  rcases he with h01 | h12 | h23 | h34 | h40
  · exact ⟨0, 1, 3, h01, h03, h13⟩
  · exact ⟨1, 2, 4, h12, h14, h24⟩
  · exact ⟨0, 2, 3, h02, h03, h23⟩
  · exact ⟨1, 3, 4, h13, h14, h34⟩
  · have h04 :
        4 ≤ circularDistance 33 (x 0).val (x 4).val := by
      have hs :
          circularDistance 33 (x 0).val (x 4).val =
          circularDistance 33 (x 4).val (x 0).val := by
        unfold circularDistance
        exact Nat.min_comm _ _
      rw [hs]
      exact h40
    exact ⟨0, 2, 4, h02, h04, h24⟩

def fiberPositions (c : Vertex → Fin 33) (b : Fin 11) :
    Finset (Fin 33) :=
  Finset.univ.biUnion fun i : Fin 5 =>
    colorInterval (c (i, b))

theorem fiberPositions_card_ge_twelve
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11) :
    12 ≤ (fiberPositions c b).card := by
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

  have hle := Finset.card_le_card hsub
  omega

end CircularColoring

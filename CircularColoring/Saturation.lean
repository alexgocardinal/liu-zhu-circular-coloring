import CircularColoring.FiberLowerBound

namespace CircularColoring

open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem mem_fiber_iff_active
    (c : Vertex → Fin 33) (b : Fin 11) (t : Fin 33) :
    t ∈ fiberPositions c b ↔ b ∈ activeFibers c t := by
  simp [fiberPositions, activeFibers]

theorem occupancy_double_count (c : Vertex → Fin 33) :
    (∑ b : Fin 11, (fiberPositions c b).card) =
    ∑ t : Fin 33, (activeFibers c t).card := by
  let r : Fin 11 → Fin 33 → Prop :=
    fun b t => t ∈ fiberPositions c b

  have above (b : Fin 11) :
      (Finset.univ : Finset (Fin 33)).bipartiteAbove r b =
      fiberPositions c b := by
    ext t
    simp [Finset.bipartiteAbove, r]

  have below (t : Fin 33) :
      (Finset.univ : Finset (Fin 11)).bipartiteBelow r t =
      activeFibers c t := by
    ext b
    simp [Finset.bipartiteBelow, r, mem_fiber_iff_active]

  have hcount :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (Fin 11)))
      (t := (Finset.univ : Finset (Fin 33))) r
  simpa only [above, below] using hcount

theorem total_occupancy
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c) :
    (∑ b : Fin 11, (fiberPositions c b).card) = 132 := by
  have hlow :
      132 ≤ ∑ b : Fin 11, (fiberPositions c b).card := by
    calc
      132 = ∑ _b : Fin 11, (12 : Nat) := by norm_num
      _ ≤ ∑ b : Fin 11, (fiberPositions c b).card := by
        apply Finset.sum_le_sum
        intro b _
        exact fiberPositions_card_ge_twelve c hc b

  have hupp :
      (∑ t : Fin 33, (activeFibers c t).card) ≤ 132 := by
    calc
      (∑ t : Fin 33, (activeFibers c t).card)
          ≤ ∑ _t : Fin 33, (4 : Nat) := by
            apply Finset.sum_le_sum
            intro t _
            exact activeFibers_card_le_four c hc t
      _ = 132 := by norm_num

  have hcount := occupancy_double_count c
  omega

theorem fiberPositions_card_eq_twelve
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11) :
    (fiberPositions c b).card = 12 := by
  have hle :
      ∀ j ∈ (Finset.univ : Finset (Fin 11)),
        (12 : Nat) ≤ (fiberPositions c j).card := by
    intro j _
    exact fiberPositions_card_ge_twelve c hc j

  have hs :
      (∑ _j : Fin 11, (12 : Nat)) =
      ∑ j : Fin 11, (fiberPositions c j).card := by
    simpa using (total_occupancy c hc).symm

  have hpoint := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  exact (hpoint b (Finset.mem_univ b)).symm

theorem activeFibers_card_eq_four
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    (activeFibers c t).card = 4 := by
  have hle :
      ∀ s ∈ (Finset.univ : Finset (Fin 33)),
        (activeFibers c s).card ≤ (4 : Nat) := by
    intro s _
    exact activeFibers_card_le_four c hc s

  have hs :
      (∑ s : Fin 33, (activeFibers c s).card) =
      ∑ _s : Fin 33, (4 : Nat) := by
    rw [← occupancy_double_count c, total_occupancy c hc]
    norm_num

  have hpoint := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  exact hpoint t (Finset.mem_univ t)

end CircularColoring

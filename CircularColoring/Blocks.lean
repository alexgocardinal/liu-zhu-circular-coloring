import CircularColoring.FiberTiling

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

structure FiberBlocks (c : Vertex → Fin 33) (b : Fin 11) where
  start : Fin 3 → Fin 33
  disjoint :
    ∀ i j : Fin 3, i ≠ j →
      Disjoint (colorInterval (start i)) (colorInterval (start j))
  covers :
    ∀ t : Fin 33,
      t ∈ fiberPositions c b ↔
      ∃ i : Fin 3, t ∈ colorInterval (start i)

theorem fiberBlocks_nonempty
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11) :
    Nonempty (FiberBlocks c b) := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hcover⟩ :=
    fiberPositions_eq_three_intervals c hc b
  refine ⟨{
    start := ![x, y, z]
    disjoint := ?_
    covers := ?_
  }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [disjoint_comm]
  · intro t
    rw [hcover]
    simp only [Finset.mem_union]
    constructor
    · intro ht
      rcases ht with (hx | hy) | hz
      · exact ⟨0, by simpa using hx⟩
      · exact ⟨1, by simpa using hy⟩
      · exact ⟨2, by simpa using hz⟩
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl (by simpa using hi))
      · exact Or.inl (Or.inr (by simpa using hi))
      · exact Or.inr (by simpa using hi)

noncomputable def chosenFiberBlocks
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11) : FiberBlocks c b :=
  Classical.choice (fiberBlocks_nonempty c hc b)

abbrev Block := Fin 11 × Fin 3

theorem number_of_blocks : Fintype.card Block = 33 := by
  decide

noncomputable def blockStart
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (q : Block) : Fin 33 :=
  (chosenFiberBlocks c hc q.1).start q.2

theorem unique_block_in_active_fiber
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11)
    (t : Fin 33)
    (ht : t ∈ fiberPositions c b) :
    ∃! i : Fin 3,
      t ∈ colorInterval (blockStart c hc (b, i)) := by
  obtain ⟨i, hi⟩ :=
    ((chosenFiberBlocks c hc b).covers t).mp ht
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  have hdis := (chosenFiberBlocks c hc b).disjoint j i hji
  exact Finset.disjoint_left.mp hdis hj hi

end CircularColoring

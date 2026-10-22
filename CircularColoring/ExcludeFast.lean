import CircularColoring.RowCapacity

namespace CircularColoring

open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem advanceSlot_succ (s : Fin 33) (k : Nat) :
    nextSlot (advanceSlot s k) = advanceSlot s (k + 1) := by
  apply Fin.ext
  dsimp [nextSlot, advanceSlot]
  omega

theorem mem_expandTimes_witness
    (A : Finset (Fin 33))
    (n : Nat) :
    ∀ x : Fin 33, x ∈ expandTimes n A →
      ∃ s ∈ A, ∃ k : Nat,
        k ≤ n ∧ x = advanceSlot s k := by
  induction n with
  | zero =>
      intro x hx
      refine ⟨x, hx, 0, by omega, ?_⟩
      exact (advanceSlot_zero x).symm
  | succ n ih =>
      intro x hx
      change x ∈ expandOnce (expandTimes n A) at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨s, hs, k, hk, hxs⟩ := ih x hx
        exact ⟨s, hs, k, by omega, hxs⟩
      · rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
        obtain ⟨s, hs, k, hk, hys⟩ := ih y hy
        refine ⟨s, hs, k + 1, by omega, ?_⟩
        calc
          x = nextSlot y := hxy.symm
          _ = nextSlot (advanceSlot s k) := congrArg nextSlot hys
          _ = advanceSlot s (k + 1) := advanceSlot_succ s k

theorem advanceSlot_mem_interval :
    ∀ (s : Fin 33) (k : Fin 4),
      advanceSlot s k.val ∈ colorInterval s := by
  decide

theorem expanded_rowColors_subset_rowPositions
    (c : Vertex → Fin 33)
    (a : Fin 5) :
    expandTimes 3 (rowColors c a) ⊆ rowPositions c a := by
  intro x hx
  obtain ⟨s, hs, k, hk, hxs⟩ :=
    mem_expandTimes_witness (rowColors c a) 3 x hx
  rcases Finset.mem_image.mp hs with ⟨b, _, hbs⟩
  have hxs' : x = advanceSlot (c (a, b)) k := by
    rw [hbs]
    exact hxs
  rw [hxs']
  apply Finset.mem_biUnion.mpr
  refine ⟨b, Finset.mem_univ b, ?_⟩
  exact advanceSlot_mem_interval (c (a, b)) ⟨k, by omega⟩

theorem fast_row_occupancy_ge_fourteen
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (initial : FiniteState)
    (hinitial : initial.2 = 0 ∨ initial.2 = 23)
    (hw : ∀ t, blockLabel c hc t =
      candidateWord fastSuccessor initial t)
    (a : Fin 5) :
    14 ≤ (rowPositions c a).card := by
  have hcolors :=
    fast_rowColors_card c hc initial hinitial hw a
  have hgrowth :=
    eleven_positions_expand_to_fourteen (rowColors c a) hcolors
  have hsub := Finset.card_le_card
    (expanded_rowColors_subset_rowPositions c a)
  omega

theorem no_fast_candidate
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (initial : FiniteState)
    (hinitial : initial.2 = 0 ∨ initial.2 = 23)
    (hw : ∀ t, blockLabel c hc t =
      candidateWord fastSuccessor initial t) :
    False := by
  have hlower :
      70 ≤ ∑ a : Fin 5, (rowPositions c a).card := by
    calc
      70 = ∑ _a : Fin 5, (14 : Nat) := by norm_num
      _ ≤ ∑ a : Fin 5, (rowPositions c a).card := by
        apply Finset.sum_le_sum
        intro a _
        exact fast_row_occupancy_ge_fourteen
          c hc initial hinitial hw a
  have hupper := total_row_occupancy_le_sixty_six c hc
  omega

end CircularColoring

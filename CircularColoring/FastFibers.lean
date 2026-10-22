import CircularColoring.IntervalPlacements

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def forwardFiberStart (a b : Fin 11) : Fin 33 :=
  ⟨(b.val + 19 - a.val) % 11, by
    have h := Nat.mod_lt (b.val + 19 - a.val) (by decide : 0 < 11)
    omega⟩

def backwardFiberStart (a b : Fin 11) : Fin 33 :=
  ⟨(a.val + 11 - b.val) % 11, by
    have h := Nat.mod_lt (a.val + 11 - b.val) (by decide : 0 < 11)
    omega⟩

-- Locate the three occurrences of each label.
theorem fast_forward_positions :
    ∀ (a b : Fin 11) (t : Fin 33),
      candidateWord fastSuccessor (a, 0) t = b ↔
        (t = forwardFiberStart a b ∨
          t = shiftColor (forwardFiberStart a b) 11 ∨
          t = shiftColor (forwardFiberStart a b) 22) := by
  decide

theorem fast_backward_positions :
    ∀ (a b : Fin 11) (t : Fin 33),
      candidateWord fastSuccessor (a, 23) t = b ↔
        (t = backwardFiberStart a b ∨
          t = shiftColor (backwardFiberStart a b) 11 ∨
          t = shiftColor (backwardFiberStart a b) 22) := by
  decide

theorem wordFiber_eq_spacedFiber
    (w : Fin 33 → Fin 11)
    (b : Fin 11)
    (p : Fin 33)
    (hpositions : ∀ s : Fin 33,
      w s = b ↔
        (s = p ∨ s = shiftColor p 11 ∨ s = shiftColor p 22)) :
    wordFiber w b = spacedFiber p := by
  ext t
  constructor
  · intro ht
    rcases (Finset.mem_filter.mp ht).2 with ⟨s, hsb, hts⟩
    rcases (hpositions s).mp hsb with hs | hs | hs
    · subst s
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl hts)))
    · subst s
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr hts)))
    · subst s
      exact Finset.mem_union.mpr (Or.inr hts)
  · intro ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact ⟨p, (hpositions p).mpr (Or.inl rfl), ht⟩
      · exact ⟨shiftColor p 11,
          (hpositions _).mpr (Or.inr (Or.inl rfl)), ht⟩
    · exact ⟨shiftColor p 22,
        (hpositions _).mpr (Or.inr (Or.inr rfl)), ht⟩

theorem fast_candidate_fiber
    (initial : FiniteState)
    (h : initial.2 = 0 ∨ initial.2 = 23)
    (b : Fin 11) :
    ∃ p : Fin 33,
      wordFiber (candidateWord fastSuccessor initial) b =
        spacedFiber p := by
  rcases initial with ⟨a, k⟩
  rcases h with h | h
  · change k = 0 at h
    subst k
    exact ⟨forwardFiberStart a b,
      wordFiber_eq_spacedFiber
        (candidateWord fastSuccessor (a, 0)) b
        (forwardFiberStart a b)
        (fast_forward_positions a b)⟩
  · change k = 23 at h
    subst k
    exact ⟨backwardFiberStart a b,
      wordFiber_eq_spacedFiber
        (candidateWord fastSuccessor (a, 23)) b
        (backwardFiberStart a b)
        (fast_backward_positions a b)⟩

theorem fast_candidate_vertex_placements
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (initial : FiniteState)
    (hinitial : initial.2 = 0 ∨ initial.2 = 23)
    (hw : ∀ t, blockLabel c hc t =
      candidateWord fastSuccessor initial t)
    (b : Fin 11) :
    ∃ p : Fin 33, ∀ a : Fin 5,
      c (a, b) = p ∨
      c (a, b) = shiftColor p 11 ∨
      c (a, b) = shiftColor p 22 := by
  obtain ⟨p, hfiber⟩ := fast_candidate_fiber initial hinitial b
  refine ⟨p, ?_⟩
  intro a
  have hallowed := coloring_uses_allowedColors c hc
    (candidateWord fastSuccessor initial) hw a b
  have hsub := (Finset.mem_filter.mp hallowed).2
  rw [hfiber] at hsub
  exact (interval_inside_spacedFiber p (c (a, b))).mp hsub

end CircularColoring

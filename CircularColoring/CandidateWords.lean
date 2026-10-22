import CircularColoring.DeterministicCycles

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def iterateState
    (step : FiniteState → FiniteState) :
    Nat → FiniteState → FiniteState
  | 0, s => s
  | n + 1, s => step (iterateState step n s)

theorem advanceSlot_from_zero :
    ∀ t : Fin 33, advanceSlot 0 t.val = t := by
  decide

theorem state_recurrence_iteration
    (s : Fin 33 → FiniteState)
    (step : FiniteState → FiniteState)
    (hstep : ∀ t, s (nextSlot t) = step (s t))
    (t : Fin 33) :
    ∀ n : Nat, n ≤ 33 →
      s (advanceSlot t n) = iterateState step n (s t) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [advanceSlot_zero]
      rfl
  | succ n ih =>
      intro hn
      have hnlt : n < 33 := by omega
      rw [← advanceSlot_step t ⟨n, hnlt⟩, hstep,
        ih (by omega)]
      rfl

theorem state_recurrence_from_zero
    (s : Fin 33 → FiniteState)
    (step : FiniteState → FiniteState)
    (hstep : ∀ t, s (nextSlot t) = step (s t))
    (t : Fin 33) :
    s t = iterateState step t.val (s 0) := by
  have h :=
    state_recurrence_iteration s step hstep 0 t.val (by omega)
  rw [advanceSlot_from_zero] at h
  exact h

theorem state_recurrence_closed
    (s : Fin 33 → FiniteState)
    (step : FiniteState → FiniteState)
    (hstep : ∀ t, s (nextSlot t) = step (s t)) :
    iterateState step 33 (s 0) = s 0 := by
  have h :=
    state_recurrence_iteration s step hstep 0 33 (by omega)
  rw [advanceSlot_thirty_three] at h
  exact h.symm

theorem fast_initial_order :
    ∀ s : FiniteState,
      (orderClass s.2 = 0 ∨ orderClass s.2 = 1) →
      FiniteFollows s (fastSuccessor s) →
      s.2 = 0 ∨ s.2 = 23 := by
  decide

theorem slow_initial_order :
    ∀ s : FiniteState,
      (orderClass s.2 = 0 ∨ orderClass s.2 = 1) →
      iterateState slowSuccessor 33 s = s →
      (s.2 = 5 ∨ s.2 = 7 ∨ s.2 = 9 ∨
        s.2 = 14 ∨ s.2 = 16 ∨ s.2 = 18) := by
  decide

def candidateWord
    (step : FiniteState → FiniteState)
    (initial : FiniteState)
    (t : Fin 33) : Fin 11 :=
  stateLabel
    (decodeState (iterateState step t.val initial)) 3

theorem coloring_word_of_recurrence
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (step : FiniteState → FiniteState)
    (hstep : ∀ t,
      encodedState c hc (nextSlot t) =
        step (encodedState c hc t))
    (t : Fin 33) :
    blockLabel c hc t =
      candidateWord step (encodedState c hc 0) t := by
  have hstate :=
    state_recurrence_from_zero (encodedState c hc) step hstep t
  have hlabel := encodedState_label c hc t 3
  rw [windowSlot_newest] at hlabel
  unfold candidateWord
  rw [← hstate]
  exact hlabel.symm

theorem coloring_candidate_words
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c) :
    (∃ initial : FiniteState,
      (initial.2 = 0 ∨ initial.2 = 23) ∧
      ∀ t, blockLabel c hc t =
        candidateWord fastSuccessor initial t) ∨
    (∃ initial : FiniteState,
      (initial.2 = 5 ∨ initial.2 = 7 ∨ initial.2 = 9 ∨
        initial.2 = 14 ∨ initial.2 = 16 ∨ initial.2 = 18) ∧
      ∀ t, blockLabel c hc t =
        candidateWord slowSuccessor initial t) := by
  rcases coloring_deterministic_cycles c hc with hfast | hslow
  · left
    refine ⟨encodedState c hc 0, ?_, ?_⟩
    · apply fast_initial_order
      · exact encodedState_class_zero_or_one c hc 0
      · have h := encodedState_follows c hc 0
        rw [hfast 0] at h
        exact h
    · exact coloring_word_of_recurrence c hc fastSuccessor hfast
  · right
    refine ⟨encodedState c hc 0, ?_, ?_⟩
    · apply slow_initial_order
      · exact encodedState_class_zero_or_one c hc 0
      · exact state_recurrence_closed
          (encodedState c hc) slowSuccessor hslow
    · exact coloring_word_of_recurrence c hc slowSuccessor hslow

end CircularColoring

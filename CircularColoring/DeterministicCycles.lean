import CircularColoring.CycleCounting

namespace CircularColoring

open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def fastSuccessor (s : FiniteState) : FiniteState :=
  if s.2 = 0 then (nextSecond s.1, 0)
  else if s.2 = 23 then (previousSecond s.1, 23)
  else s

def slowSuccessor (s : FiniteState) : FiniteState :=
  match s.2.val with
  | 0 => (s.1, 9)
  | 9 => (s.1, 16)
  | 16 => (s.1, 18)
  | 18 => (previousSecond s.1, 9)
  | 23 => (s.1, 14)
  | 14 => (s.1, 7)
  | 7 => (s.1, 5)
  | 5 => (nextSecond s.1, 14)
  | _ => s

theorem fastStep_le_one (u v : FiniteState) :
    fastStep u v ≤ 1 := by
  unfold fastStep
  split <;> omega

theorem fast_transition_determined :
    ∀ u v : FiniteState,
      (orderClass u.2 = 0 ∨ orderClass u.2 = 1) →
      FiniteFollows u v →
      fastStep u v = 1 →
      v = fastSuccessor u := by
  decide

theorem slow_transition_determined :
    ∀ u v : FiniteState,
      (orderClass u.2 = 0 ∨ orderClass u.2 = 1) →
      FiniteFollows u v →
      fastStep u v = 0 →
      phaseWrap u v = 0 →
      v = slowSuccessor u := by
  decide

theorem all_zero_of_sum_zero
    (f : Fin 33 → Nat)
    (h : (∑ t : Fin 33, f t) = 0) :
    ∀ t, f t = 0 := by
  have hle :
      ∀ t ∈ (Finset.univ : Finset (Fin 33)),
        (0 : Nat) ≤ f t := by
    intro t _
    exact Nat.zero_le _
  have hs :
      (∑ _t : Fin 33, (0 : Nat)) =
        ∑ t : Fin 33, f t := by
    simpa using h.symm
  have hpoint := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  intro t
  exact (hpoint t (Finset.mem_univ t)).symm

theorem all_one_of_sum_thirty_three
    (f : Fin 33 → Nat)
    (hle : ∀ t, f t ≤ 1)
    (h : (∑ t : Fin 33, f t) = 33) :
    ∀ t, f t = 1 := by
  have hle' :
      ∀ t ∈ (Finset.univ : Finset (Fin 33)),
        f t ≤ (1 : Nat) := by
    intro t _
    exact hle t
  have hs :
      (∑ t : Fin 33, f t) =
        ∑ _t : Fin 33, (1 : Nat) := by
    simpa using h
  have hpoint := (Finset.sum_eq_sum_iff_of_le hle').mp hs
  intro t
  exact hpoint t (Finset.mem_univ t)

theorem coloring_deterministic_cycles
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c) :
    (∀ t : Fin 33,
      encodedState c hc (nextSlot t) =
        fastSuccessor (encodedState c hc t)) ∨
    (∀ t : Fin 33,
      encodedState c hc (nextSlot t) =
        slowSuccessor (encodedState c hc t)) := by
  rcases coloring_two_transition_patterns c hc with
    ⟨hfast, _, _⟩ | ⟨hfast, _, hwrap⟩
  · left
    change
      (∑ t : Fin 33,
        fastStep (encodedState c hc t)
          (encodedState c hc (nextSlot t))) = 33 at hfast
    have hone := all_one_of_sum_thirty_three
      (fun t => fastStep (encodedState c hc t)
        (encodedState c hc (nextSlot t)))
      (fun t => fastStep_le_one _ _) hfast
    intro t
    exact fast_transition_determined
      (encodedState c hc t)
      (encodedState c hc (nextSlot t))
      (encodedState_class_zero_or_one c hc t)
      (encodedState_follows c hc t)
      (hone t)
  · right
    change
      (∑ t : Fin 33,
        fastStep (encodedState c hc t)
          (encodedState c hc (nextSlot t))) = 0 at hfast
    change
      (∑ t : Fin 33,
        phaseWrap (encodedState c hc t)
          (encodedState c hc (nextSlot t))) = 0 at hwrap
    have hzero := all_zero_of_sum_zero
      (fun t => fastStep (encodedState c hc t)
        (encodedState c hc (nextSlot t))) hfast
    have hnowrap := all_zero_of_sum_zero
      (fun t => phaseWrap (encodedState c hc t)
        (encodedState c hc (nextSlot t))) hwrap
    intro t
    exact slow_transition_determined
      (encodedState c hc t)
      (encodedState c hc (nextSlot t))
      (encodedState_class_zero_or_one c hc t)
      (encodedState_follows c hc t)
      (hzero t) (hnowrap t)

end CircularColoring

import CircularColoring.TransitionAccounting

namespace CircularColoring

open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem nextSlot_injective :
    Function.Injective nextSlot := by
  decide

theorem nextSlot_previousSlot :
    ∀ t : Fin 33, nextSlot (previousSlot t) = t := by
  decide

-- Rotating the indices does not change a sum around the circle.
theorem sum_nextSlot (f : Fin 33 → Nat) :
    (∑ t : Fin 33, f (nextSlot t)) =
      ∑ t : Fin 33, f t := by
  apply Finset.sum_bij (fun t _ => nextSlot t)
  · intro t _
    exact Finset.mem_univ _
  · intro a _ b _ hab
    exact nextSlot_injective hab
  · intro b _
    exact ⟨previousSlot b, Finset.mem_univ _,
      nextSlot_previousSlot b⟩
  · intro t _
    rfl

structure TransitionTotals where
  fast : Nat
  slow : Nat
  wraps : Nat
  up : Nat
  down : Nat

def transitionTotals (s : Fin 33 → FiniteState) : TransitionTotals :=
  { fast := ∑ t : Fin 33, fastStep (s t) (s (nextSlot t))
    slow := ∑ t : Fin 33, slowStep (s t) (s (nextSlot t))
    wraps := ∑ t : Fin 33, phaseWrap (s t) (s (nextSlot t))
    up := ∑ t : Fin 33, arcWrapUp (s t) (s (nextSlot t))
    down := ∑ t : Fin 33, arcWrapDown (s t) (s (nextSlot t)) }

theorem closed_walk_totals
    (s : Fin 33 → FiniteState)
    (hclass : ∀ t, orderClass (s t).2 = 0 ∨
      orderClass (s t).2 = 1)
    (hstep : ∀ t, FiniteFollows (s t) (s (nextSlot t))) :
    (33 = 4 * (transitionTotals s).wraps +
      (transitionTotals s).fast + 3 * (transitionTotals s).slow) ∧
    ((transitionTotals s).slow + 11 * (transitionTotals s).up =
      (transitionTotals s).fast + 11 * (transitionTotals s).down) := by
  have hp :
      (∑ t : Fin 33,
        (orderPhase (s (nextSlot t)).2 +
          4 * phaseWrap (s t) (s (nextSlot t)) +
          fastStep (s t) (s (nextSlot t)) +
          3 * slowStep (s t) (s (nextSlot t)))) =
      ∑ t : Fin 33, (orderPhase (s t).2 + 1) := by
    apply Finset.sum_congr rfl
    intro t _
    exact (transition_accounting
      (s t) (s (nextSlot t)) (hclass t) (hstep t)).1

  have ha :
      (∑ t : Fin 33,
        (orientedArc (s (nextSlot t)) +
          slowStep (s t) (s (nextSlot t)) +
          11 * arcWrapUp (s t) (s (nextSlot t)))) =
      ∑ t : Fin 33,
        (orientedArc (s t) +
          fastStep (s t) (s (nextSlot t)) +
          11 * arcWrapDown (s t) (s (nextSlot t))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact (transition_accounting
      (s t) (s (nextSlot t)) (hclass t) (hstep t)).2

  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hp ha
  rw [sum_nextSlot (fun t => orderPhase (s t).2)] at hp
  rw [sum_nextSlot (fun t => orientedArc (s t))] at ha
  norm_num at hp
  dsimp only [transitionTotals]
  constructor <;> omega

theorem closed_walk_two_patterns
    (s : Fin 33 → FiniteState)
    (hclass : ∀ t, orderClass (s t).2 = 0 ∨
      orderClass (s t).2 = 1)
    (hstep : ∀ t, FiniteFollows (s t) (s (nextSlot t))) :
    ((transitionTotals s).fast = 33 ∧
      (transitionTotals s).slow = 0 ∧
      (transitionTotals s).wraps = 0) ∨
    ((transitionTotals s).fast = 0 ∧
      (transitionTotals s).slow = 11 ∧
      (transitionTotals s).wraps = 0) := by
  obtain ⟨hp, ha⟩ := closed_walk_totals s hclass hstep
  exact thirty_three_step_counting
    (transitionTotals s).fast
    (transitionTotals s).slow
    (transitionTotals s).wraps
    (transitionTotals s).up
    (transitionTotals s).down hp ha

theorem coloring_two_transition_patterns
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c) :
    ((transitionTotals (encodedState c hc)).fast = 33 ∧
      (transitionTotals (encodedState c hc)).slow = 0 ∧
      (transitionTotals (encodedState c hc)).wraps = 0) ∨
    ((transitionTotals (encodedState c hc)).fast = 0 ∧
      (transitionTotals (encodedState c hc)).slow = 11 ∧
      (transitionTotals (encodedState c hc)).wraps = 0) := by
  exact closed_walk_two_patterns
    (encodedState c hc)
    (encodedState_class_zero_or_one c hc)
    (encodedState_follows c hc)

end CircularColoring

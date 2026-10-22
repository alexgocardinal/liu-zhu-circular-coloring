import CircularColoring.StateParity

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

-- Treat the two orientations in the same way.
def orientedArc (s : FiniteState) : Nat :=
  if orderClass s.2 = 1 then
    (18 - s.1.val) % 11
  else
    s.1.val

def orderPhase (k : Fin 24) : Nat :=
  if k = 0 ∨ k = 23 then 0
  else if k = 9 ∨ k = 14 then 1
  else if k = 16 ∨ k = 7 then 2
  else 3

def fastStep (u v : FiniteState) : Nat :=
  if (u.2 = 0 ∧ v.2 = 0) ∨
      (u.2 = 23 ∧ v.2 = 23) then 1 else 0

def slowStep (u v : FiniteState) : Nat :=
  if (u.2 = 18 ∧ v.2 = 9) ∨
      (u.2 = 5 ∧ v.2 = 14) then 1 else 0

def phaseWrap (u v : FiniteState) : Nat :=
  if (u.2 = 18 ∧ v.2 = 0) ∨
      (u.2 = 5 ∧ v.2 = 23) then 1 else 0

def arcWrapUp (u v : FiniteState) : Nat :=
  if orientedArc u = 10 ∧ fastStep u v = 1 then 1 else 0

def arcWrapDown (u v : FiniteState) : Nat :=
  if orientedArc u = 0 ∧ slowStep u v = 1 then 1 else 0

-- Check both counting identities for every relevant transition.
theorem transition_accounting :
    ∀ u v : FiniteState,
      (orderClass u.2 = 0 ∨ orderClass u.2 = 1) →
      FiniteFollows u v →
      (orderPhase v.2 + 4 * phaseWrap u v +
          fastStep u v + 3 * slowStep u v =
        orderPhase u.2 + 1) ∧
      (orientedArc v + slowStep u v + 11 * arcWrapUp u v =
        orientedArc u + fastStep u v + 11 * arcWrapDown u v) := by
  decide

-- The resulting arithmetic leaves exactly two possibilities.
theorem thirty_three_step_counting
    (fast slow wraps up down : Nat)
    (hphase : 33 = 4 * wraps + fast + 3 * slow)
    (harc : slow + 11 * up = fast + 11 * down) :
    (fast = 33 ∧ slow = 0 ∧ wraps = 0) ∨
    (fast = 0 ∧ slow = 11 ∧ wraps = 0) := by
  omega

theorem encodedState_transition_accounting
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    let u := encodedState c hc t
    let v := encodedState c hc (nextSlot t)
    (orderPhase v.2 + 4 * phaseWrap u v +
        fastStep u v + 3 * slowStep u v =
      orderPhase u.2 + 1) ∧
    (orientedArc v + slowStep u v + 11 * arcWrapUp u v =
      orientedArc u + fastStep u v + 11 * arcWrapDown u v) := by
  exact transition_accounting
    (encodedState c hc t)
    (encodedState c hc (nextSlot t))
    (encodedState_class_zero_or_one c hc t)
    (encodedState_follows c hc t)

end CircularColoring

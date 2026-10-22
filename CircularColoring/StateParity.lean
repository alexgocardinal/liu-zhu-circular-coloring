import CircularColoring.FiniteStates

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

-- Classes 0 and 1 contain the eight surviving orders.
-- Classes 2 and 3 alternate at every legal transition.
def orderClass (k : Fin 24) : Fin 4 :=
  if k.val = 0 ∨ k.val = 9 ∨ k.val = 16 ∨ k.val = 18 then
    0
  else if k.val = 5 ∨ k.val = 7 ∨ k.val = 14 ∨ k.val = 23 then
    1
  else if k.val = 1 ∨ k.val = 4 ∨ k.val = 6 ∨ k.val = 8 ∨
      k.val = 15 ∨ k.val = 17 ∨ k.val = 19 ∨ k.val = 22 then
    2
  else
    3

def nextClass (k : Fin 4) : Fin 4 :=
  if k = 2 then 3 else if k = 3 then 2 else k

-- A finite check of the transition rule for all 264 states.
theorem finiteFollows_class :
    ∀ u v : FiniteState,
      FiniteFollows u v →
      orderClass v.2 = nextClass (orderClass u.2) := by
  decide

def iterateClass : Nat → Fin 4 → Fin 4
  | 0, k => k
  | n + 1, k => nextClass (iterateClass n k)

theorem class_fixed_after_thirty_three :
    ∀ k : Fin 4,
      iterateClass 33 k = k →
      k = 0 ∨ k = 1 := by
  decide

theorem encodedState_class_iteration
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    ∀ n : Nat, n ≤ 33 →
      orderClass (encodedState c hc (advanceSlot t n)).2 =
        iterateClass n (orderClass (encodedState c hc t).2) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [advanceSlot_zero]
      rfl
  | succ n ih =>
      intro hn
      have hnlt : n < 33 := by omega
      have hstep :=
        finiteFollows_class
          (encodedState c hc (advanceSlot t n))
          (encodedState c hc (nextSlot (advanceSlot t n)))
          (encodedState_follows c hc (advanceSlot t n))
      rw [advanceSlot_step t ⟨n, hnlt⟩] at hstep
      rw [hstep, ih (by omega)]
      rfl

theorem encodedState_class_zero_or_one
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    orderClass (encodedState c hc t).2 = 0 ∨
      orderClass (encodedState c hc t).2 = 1 := by
  have h :=
    encodedState_class_iteration c hc t 33 (by omega)
  rw [advanceSlot_thirty_three] at h
  exact class_fixed_after_thirty_three _ h.symm

-- Translate the class restriction back into explicit order indices.
theorem surviving_order_indices :
    ∀ k : Fin 24,
      (orderClass k = 0 ∨ orderClass k = 1) →
      (k = 0 ∨ k = 5 ∨ k = 7 ∨ k = 9 ∨
        k = 14 ∨ k = 16 ∨ k = 18 ∨ k = 23) := by
  decide

theorem encodedState_eight_orders
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    (encodedState c hc t).2 = 0 ∨
    (encodedState c hc t).2 = 5 ∨
    (encodedState c hc t).2 = 7 ∨
    (encodedState c hc t).2 = 9 ∨
    (encodedState c hc t).2 = 14 ∨
    (encodedState c hc t).2 = 16 ∨
    (encodedState c hc t).2 = 18 ∨
    (encodedState c hc t).2 = 23 := by
  exact surviving_order_indices _
    (encodedState_class_zero_or_one c hc t)

end CircularColoring

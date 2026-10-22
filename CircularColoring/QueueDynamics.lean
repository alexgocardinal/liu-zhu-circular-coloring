import CircularColoring.WindowOrder

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def nextSlot (t : Fin 33) : Fin 33 :=
  ⟨(t.val + 1) % 33, Nat.mod_lt _ (by decide)⟩

def advanceSlot (t : Fin 33) (n : Nat) : Fin 33 :=
  ⟨(t.val + n) % 33, Nat.mod_lt _ (by decide)⟩

-- Moving the window retains its three newest positions.
theorem windowSlot_shift :
    ∀ (t : Fin 33) (i : Fin 3),
      windowSlot (nextSlot t) i.castSucc =
        windowSlot t i.succ := by
  decide

theorem advanceSlot_zero :
    ∀ t : Fin 33, advanceSlot t 0 = t := by
  decide

theorem advanceSlot_thirty_three :
    ∀ t : Fin 33, advanceSlot t 33 = t := by
  decide

theorem advanceSlot_step :
    ∀ (t : Fin 33) (n : Fin 33),
      nextSlot (advanceSlot t n.val) =
        advanceSlot t (n.val + 1) := by
  decide

structure WindowState where
  arcStart : Fin 11
  order : Fin 4 → Fin 4
  order_injective : Function.Injective order

def stateLabel (s : WindowState) (i : Fin 4) : Fin 11 :=
  addSecond s.arcStart (s.order i).val

-- A legal transition preserves the three retained labels.
def QueueFollows (u v : WindowState) : Prop :=
  ∀ i : Fin 3,
    stateLabel v i.castSucc = stateLabel u i.succ

instance (u v : WindowState) : Decidable (QueueFollows u v) := by
  unfold QueueFollows
  infer_instance

noncomputable def actualState
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : WindowState :=
  { arcStart := windowArcStart c hc t
    order := windowOrder c hc t
    order_injective := windowOrder_injective c hc t }

theorem actualState_label
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (i : Fin 4) :
    stateLabel (actualState c hc t) i =
      blockLabel c hc (windowSlot t i) := by
  exact windowOrder_reconstruct c hc t i

theorem actualState_follows
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    QueueFollows (actualState c hc t)
      (actualState c hc (nextSlot t)) := by
  intro i
  rw [actualState_label, actualState_label, windowSlot_shift]

theorem actualState_closed
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    actualState c hc (advanceSlot t 33) =
      actualState c hc t := by
  rw [advanceSlot_thirty_three]

theorem actualState_walk
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (n : Fin 33) :
    QueueFollows
      (actualState c hc (advanceSlot t n.val))
      (actualState c hc (advanceSlot t (n.val + 1))) := by
  rw [← advanceSlot_step t n]
  exact actualState_follows c hc (advanceSlot t n.val)

end CircularColoring

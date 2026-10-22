import CircularColoring.QueueDynamics

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- All 24 permutations of the four offsets.
def orderTable : Fin 24 → (Fin 4 → Fin 4) :=
  ![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 3, 1, 2],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![1, 3, 0, 2],
    ![1, 3, 2, 0],
    ![2, 0, 1, 3],
    ![2, 0, 3, 1],
    ![2, 1, 0, 3],
    ![2, 1, 3, 0],
    ![2, 3, 0, 1],
    ![2, 3, 1, 0],
    ![3, 0, 1, 2],
    ![3, 0, 2, 1],
    ![3, 1, 0, 2],
    ![3, 1, 2, 0],
    ![3, 2, 0, 1],
    ![3, 2, 1, 0]]

theorem orderTable_injective :
    ∀ k : Fin 24, Function.Injective (orderTable k) := by
  decide

theorem orderTable_complete :
    ∀ f : Fin 4 → Fin 4,
      Function.Injective f →
      ∃ k : Fin 24, orderTable k = f := by
  decide

abbrev FiniteState := Fin 11 × Fin 24

theorem number_of_finite_states :
    Fintype.card FiniteState = 264 := by
  decide

def decodeState (s : FiniteState) : WindowState :=
  { arcStart := s.1
    order := orderTable s.2
    order_injective := orderTable_injective s.2 }

def FiniteFollows (u v : FiniteState) : Prop :=
  QueueFollows (decodeState u) (decodeState v)

instance (u v : FiniteState) : Decidable (FiniteFollows u v) := by
  unfold FiniteFollows
  infer_instance

noncomputable def orderIndex
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : Fin 24 :=
  Classical.choose
    (orderTable_complete (windowOrder c hc t)
      (windowOrder_injective c hc t))

theorem orderIndex_spec
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    orderTable (orderIndex c hc t) = windowOrder c hc t :=
  Classical.choose_spec
    (orderTable_complete (windowOrder c hc t)
      (windowOrder_injective c hc t))

noncomputable def encodedState
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : FiniteState :=
  (windowArcStart c hc t, orderIndex c hc t)

theorem encodedState_label
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (i : Fin 4) :
    stateLabel (decodeState (encodedState c hc t)) i =
      blockLabel c hc (windowSlot t i) := by
  change
    addSecond (windowArcStart c hc t)
      (orderTable (orderIndex c hc t) i).val =
        blockLabel c hc (windowSlot t i)
  rw [orderIndex_spec]
  exact windowOrder_reconstruct c hc t i

theorem encodedState_follows
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    FiniteFollows (encodedState c hc t)
      (encodedState c hc (nextSlot t)) := by
  intro i
  rw [encodedState_label, encodedState_label, windowSlot_shift]

theorem encodedState_closed
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    encodedState c hc (advanceSlot t 33) =
      encodedState c hc t := by
  rw [advanceSlot_thirty_three]

end CircularColoring

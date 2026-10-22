import CircularColoring.StationaryWindows

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def addSecond (b : Fin 11) (k : Nat) : Fin 11 :=
  ⟨(b.val + k) % 11, Nat.mod_lt _ (by decide)⟩

theorem retained_previous_slot_mem_current_window :
    ∀ t s : Fin 33,
      s ∈ fourSlotWindow (previousSlot t) →
      s ≠ backFour t →
      s ∈ fourSlotWindow t := by
  decide

-- A label present only in the new window must be the entering label.
theorem entering_label_of_new_member
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (b : Fin 11)
    (hb : b ∈ windowLabels c hc t)
    (hnot : b ∉ windowLabels c hc (previousSlot t)) :
    blockLabel c hc t = b := by
  rcases Finset.mem_image.mp hb with ⟨s, hs, hsb⟩
  by_cases hst : s = t
  · subst s
    exact hsb
  · exact False.elim
      (hnot (Finset.mem_image.mpr
        ⟨s, retained_slot_mem_previous_window t s hs hst, hsb⟩))

-- A label present only in the old window must be the departing label.
theorem departing_label_of_old_member
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (b : Fin 11)
    (hb : b ∈ windowLabels c hc (previousSlot t))
    (hnot : b ∉ windowLabels c hc t) :
    blockLabel c hc (backFour t) = b := by
  rcases Finset.mem_image.mp hb with ⟨s, hs, hsb⟩
  by_cases hst : s = backFour t
  · subst s
    exact hsb
  · exact False.elim
      (hnot (Finset.mem_image.mpr
        ⟨s, retained_previous_slot_mem_current_window t s hs hst,
          hsb⟩))

theorem forward_arc_endpoints :
    ∀ s : Fin 11,
      (addSecond s 4 ∈ secondArc (nextSecond s) ∧
        addSecond s 4 ∉ secondArc s) ∧
      (s ∈ secondArc s ∧ s ∉ secondArc (nextSecond s)) := by
  decide

theorem backward_arc_endpoints :
    ∀ s : Fin 11,
      (previousSecond s ∈ secondArc (previousSecond s) ∧
        previousSecond s ∉ secondArc s) ∧
      (addSecond s 3 ∈ secondArc s ∧
        addSecond s 3 ∉ secondArc (previousSecond s)) := by
  decide

theorem forward_move_labels
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (h :
      windowArcStart c hc t =
        nextSecond (windowArcStart c hc (previousSlot t))) :
    blockLabel c hc t =
        addSecond (windowArcStart c hc (previousSlot t)) 4 ∧
    blockLabel c hc (backFour t) =
        windowArcStart c hc (previousSlot t) := by
  have hend :=
    forward_arc_endpoints (windowArcStart c hc (previousSlot t))
  constructor
  · apply entering_label_of_new_member c hc t
    · rw [windowArcStart_spec c hc t, h]
      exact hend.1.1
    · rw [windowArcStart_spec c hc (previousSlot t)]
      exact hend.1.2
  · apply departing_label_of_old_member c hc t
    · rw [windowArcStart_spec c hc (previousSlot t)]
      exact hend.2.1
    · rw [windowArcStart_spec c hc t, h]
      exact hend.2.2

theorem backward_move_labels
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (h :
      windowArcStart c hc t =
        previousSecond (windowArcStart c hc (previousSlot t))) :
    blockLabel c hc t =
        previousSecond (windowArcStart c hc (previousSlot t)) ∧
    blockLabel c hc (backFour t) =
        addSecond (windowArcStart c hc (previousSlot t)) 3 := by
  have hend :=
    backward_arc_endpoints (windowArcStart c hc (previousSlot t))
  constructor
  · apply entering_label_of_new_member c hc t
    · rw [windowArcStart_spec c hc t, h]
      exact hend.1.1
    · rw [windowArcStart_spec c hc (previousSlot t)]
      exact hend.1.2
  · apply departing_label_of_old_member c hc t
    · rw [windowArcStart_spec c hc (previousSlot t)]
      exact hend.2.1
    · rw [windowArcStart_spec c hc t, h]
      exact hend.2.2

end CircularColoring

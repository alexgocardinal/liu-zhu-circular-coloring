import CircularColoring.ArcTransitions

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem current_slot_mem_window :
    ∀ t : Fin 33, t ∈ fourSlotWindow t := by
  decide

theorem departing_slot_mem_previous_window :
    ∀ t : Fin 33,
      backFour t ∈ fourSlotWindow (previousSlot t) := by
  decide

theorem departing_slot_not_mem_current_window :
    ∀ t : Fin 33,
      backFour t ∉ fourSlotWindow t := by
  decide

theorem retained_slot_mem_previous_window :
    ∀ t s : Fin 33,
      s ∈ fourSlotWindow t →
      s ≠ t →
      s ∈ fourSlotWindow (previousSlot t) := by
  decide

theorem secondArc_injective :
    ∀ a b : Fin 11, secondArc a = secondArc b → a = b := by
  decide

theorem stationary_arc_repeats_label
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (h :
      windowArcStart c hc t =
        windowArcStart c hc (previousSlot t)) :
    blockLabel c hc t = blockLabel c hc (backFour t) := by
  have heq :
      windowLabels c hc t =
        windowLabels c hc (previousSlot t) := by
    rw [windowArcStart_spec c hc t,
      windowArcStart_spec c hc (previousSlot t), h]

  have hold :
      blockLabel c hc (backFour t) ∈
        windowLabels c hc (previousSlot t) :=
    Finset.mem_image.mpr
      ⟨backFour t, departing_slot_mem_previous_window t, rfl⟩

  have hcurrent :
      blockLabel c hc (backFour t) ∈ windowLabels c hc t := by
    rw [heq]
    exact hold

  rcases Finset.mem_image.mp hcurrent with ⟨s, hs, hlabel⟩
  by_cases hst : s = t
  · subst s
    exact hlabel
  · have hsold :
        s ∈ fourSlotWindow (previousSlot t) :=
      retained_slot_mem_previous_window t s hs hst
    have hsback : s = backFour t :=
      blockLabel_injective_on_window c hc (previousSlot t)
        hsold (departing_slot_mem_previous_window t) hlabel
    exact False.elim
      (departing_slot_not_mem_current_window t (hsback ▸ hs))

theorem repeated_label_keeps_arc_stationary
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (h : blockLabel c hc t = blockLabel c hc (backFour t)) :
    windowArcStart c hc t =
      windowArcStart c hc (previousSlot t) := by
  have hsub :
      windowLabels c hc t ⊆
        windowLabels c hc (previousSlot t) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨s, hs, hsb⟩
    by_cases hst : s = t
    · subst s
      apply Finset.mem_image.mpr
      refine ⟨backFour t,
        departing_slot_mem_previous_window t, ?_⟩
      exact h.symm.trans hsb
    · exact Finset.mem_image.mpr
        ⟨s, retained_slot_mem_previous_window t s hs hst, hsb⟩

  have heq :
      windowLabels c hc t =
        windowLabels c hc (previousSlot t) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [windowLabels_card_eq_four c hc (previousSlot t),
      windowLabels_card_eq_four c hc t]

  apply secondArc_injective
  rw [← windowArcStart_spec c hc t,
    ← windowArcStart_spec c hc (previousSlot t)]
  exact heq

theorem stationary_arc_iff_repeated_label
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    (windowArcStart c hc t =
      windowArcStart c hc (previousSlot t)) ↔
    (blockLabel c hc t = blockLabel c hc (backFour t)) := by
  constructor
  · exact stationary_arc_repeats_label c hc t
  · exact repeated_label_keeps_arc_stationary c hc t

end CircularColoring

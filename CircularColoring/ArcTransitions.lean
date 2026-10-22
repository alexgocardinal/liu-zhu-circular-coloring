import CircularColoring.WordWindows

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def nextSecond (b : Fin 11) : Fin 11 :=
  ⟨(b.val + 1) % 11, Nat.mod_lt _ (by decide)⟩

def previousSecond (b : Fin 11) : Fin 11 :=
  ⟨(b.val + 10) % 11, Nat.mod_lt _ (by decide)⟩

-- Two four-label arcs sharing three labels have nearby starts.
theorem overlapping_arcs_nearby :
    ∀ s r : Fin 11,
      3 ≤ (secondArc s ∩ secondArc r).card →
      (r = s ∨ r = nextSecond s ∨ r = previousSecond s) := by
  decide

-- Consecutive windows share exactly three positions.
theorem consecutive_windows_intersection_card :
    ∀ t : Fin 33,
      (fourSlotWindow t ∩
        fourSlotWindow (previousSlot t)).card = 3 := by
  decide

noncomputable def windowArcStart
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : Fin 11 :=
  Classical.choose ((windowLabels_is_arc c hc t).exists)

theorem windowArcStart_spec
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    windowLabels c hc t = secondArc (windowArcStart c hc t) :=
  Classical.choose_spec ((windowLabels_is_arc c hc t).exists)

theorem consecutive_window_labels_overlap
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    3 ≤
      (windowLabels c hc t ∩
        windowLabels c hc (previousSlot t)).card := by
  let shared : Finset (Fin 33) :=
    fourSlotWindow t ∩ fourSlotWindow (previousSlot t)

  have hinj : Set.InjOn (blockLabel c hc) shared := by
    intro s hs r hr heq
    exact blockLabel_injective_on_window c hc t
      (Finset.mem_inter.mp hs).1
      (Finset.mem_inter.mp hr).1 heq

  have himage :
      (shared.image (blockLabel c hc)).card = shared.card :=
    Finset.card_image_of_injOn hinj

  have hsub :
      shared.image (blockLabel c hc) ⊆
        windowLabels c hc t ∩
          windowLabels c hc (previousSlot t) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨s, hs, hsb⟩
    have hs' :
        s ∈ fourSlotWindow t ∧
          s ∈ fourSlotWindow (previousSlot t) :=
      Finset.mem_inter.mp hs
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨s, hs'.1, hsb⟩
    · exact Finset.mem_image.mpr ⟨s, hs'.2, hsb⟩

  have hle := Finset.card_le_card hsub
  have hthree : shared.card = 3 :=
    consecutive_windows_intersection_card t
  rw [himage, hthree] at hle
  exact hle

theorem windowArcStart_transition
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    windowArcStart c hc (previousSlot t) = windowArcStart c hc t ∨
    windowArcStart c hc (previousSlot t) =
      nextSecond (windowArcStart c hc t) ∨
    windowArcStart c hc (previousSlot t) =
      previousSecond (windowArcStart c hc t) := by
  apply overlapping_arcs_nearby
  have h := consecutive_window_labels_overlap c hc t
  rw [windowArcStart_spec c hc t,
    windowArcStart_spec c hc (previousSlot t)] at h
  exact h

end CircularColoring

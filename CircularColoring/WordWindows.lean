import CircularColoring.BlockWord

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

-- The four positions ending at t.
def fourSlotWindow (t : Fin 33) : Finset (Fin 33) :=
  {t, previousSlot t,
    previousSlot (previousSlot t),
    previousSlot (previousSlot (previousSlot t))}

theorem fourSlotWindow_card :
    ∀ t : Fin 33, (fourSlotWindow t).card = 4 := by
  decide

-- An interval covers t exactly when its start is in this window.
theorem mem_interval_iff_start_window :
    ∀ s t : Fin 33,
      t ∈ colorInterval s ↔ s ∈ fourSlotWindow t := by
  decide

noncomputable def windowLabels
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : Finset (Fin 11) :=
  (fourSlotWindow t).image (blockLabel c hc)

theorem windowLabels_eq_active
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    windowLabels c hc t = activeFibers c t := by
  ext b
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨s, hs, hsb⟩
    have hpos : t ∈ colorInterval s :=
      (mem_interval_iff_start_window s t).mpr hs
    have hblock :
        t ∈ colorInterval
          (blockStart c hc (blockAt c hc s)) := by
      rw [blockAt_start]
      exact hpos
    have hf :
        t ∈ fiberPositions c (blockAt c hc s).1 :=
      ((chosenFiberBlocks c hc (blockAt c hc s).1).covers t).mpr
        ⟨(blockAt c hc s).2, hblock⟩
    have hactive :
        blockLabel c hc s ∈ activeFibers c t :=
      (mem_fiber_iff_active c (blockLabel c hc s) t).mp hf
    exact hsb ▸ hactive
  · intro hb
    have ht : t ∈ fiberPositions c b :=
      (mem_fiber_iff_active c b t).mpr hb
    obtain ⟨i, hi, _⟩ :=
      unique_block_in_active_fiber c hc b t ht
    let q : Block := (b, i)
    refine Finset.mem_image.mpr
      ⟨blockStart c hc q, ?_, ?_⟩
    · exact (mem_interval_iff_start_window _ t).mp hi
    · change (blockAt c hc (blockStart c hc q)).1 = b
      rw [blockAt_of_start]

theorem windowLabels_card_eq_four
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    (windowLabels c hc t).card = 4 := by
  rw [windowLabels_eq_active]
  exact activeFibers_card_eq_four c hc t

theorem blockLabel_injective_on_window
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    Set.InjOn (blockLabel c hc) (fourSlotWindow t) := by
  apply Finset.card_image_iff.mp
  change
    (windowLabels c hc t).card = (fourSlotWindow t).card
  rw [windowLabels_card_eq_four c hc t, fourSlotWindow_card t]

theorem windowLabels_is_arc
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    ∃! start : Fin 11,
      windowLabels c hc t = secondArc start := by
  rw [windowLabels_eq_active]
  exact activeFibers_is_arc c hc t

end CircularColoring

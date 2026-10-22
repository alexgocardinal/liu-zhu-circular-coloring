import CircularColoring.MovingWindows

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

-- List the window's positions from oldest to newest.
def windowSlot (t : Fin 33) (i : Fin 4) : Fin 33 :=
  ⟨(t.val + 30 + i.val) % 33, Nat.mod_lt _ (by decide)⟩

theorem windowSlot_mem :
    ∀ (t : Fin 33) (i : Fin 4),
      windowSlot t i ∈ fourSlotWindow t := by
  decide

theorem windowSlot_injective :
    ∀ t : Fin 33, Function.Injective (windowSlot t) := by
  decide

theorem windowSlot_newest :
    ∀ t : Fin 33, windowSlot t 3 = t := by
  decide

-- Recover a label from its offset within an arc.
theorem addSecond_relative :
    ∀ s b : Fin 11,
      addSecond s ((b.val + 11 - s.val) % 11) = b := by
  decide

-- Replace the four actual labels by their offsets 0, 1, 2, 3.
noncomputable def windowOrder
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (i : Fin 4) : Fin 4 :=
  ⟨((blockLabel c hc (windowSlot t i)).val + 11 -
      (windowArcStart c hc t).val) % 11, by
    have hmem :
        blockLabel c hc (windowSlot t i) ∈
          windowLabels c hc t :=
      Finset.mem_image.mpr
        ⟨windowSlot t i, windowSlot_mem t i, rfl⟩
    rw [windowArcStart_spec c hc t] at hmem
    exact (Finset.mem_filter.mp hmem).2⟩

theorem windowOrder_reconstruct
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33)
    (i : Fin 4) :
    addSecond (windowArcStart c hc t)
        (windowOrder c hc t i).val =
      blockLabel c hc (windowSlot t i) := by
  exact addSecond_relative
    (windowArcStart c hc t)
    (blockLabel c hc (windowSlot t i))

theorem windowOrder_injective
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    Function.Injective (windowOrder c hc t) := by
  intro i j hij
  have hlabels :
      blockLabel c hc (windowSlot t i) =
        blockLabel c hc (windowSlot t j) := by
    have h := congrArg
      (fun k : Fin 4 =>
        addSecond (windowArcStart c hc t) k.val) hij
    simpa only [windowOrder_reconstruct] using h
  have hslots : windowSlot t i = windowSlot t j :=
    blockLabel_injective_on_window c hc t
      (windowSlot_mem t i) (windowSlot_mem t j) hlabels
  exact windowSlot_injective t hslots

end CircularColoring

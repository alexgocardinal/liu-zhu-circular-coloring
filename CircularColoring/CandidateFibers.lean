import CircularColoring.CandidateWords

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- Positions occupied by a label in a proposed block sequence.
def wordFiber
    (w : Fin 33 → Fin 11)
    (b : Fin 11) : Finset (Fin 33) :=
  Finset.univ.filter fun t =>
    ∃ s : Fin 33, w s = b ∧ t ∈ colorInterval s

-- A vertex's four-position interval must fit inside its fiber.
def allowedColors
    (w : Fin 33 → Fin 11)
    (b : Fin 11) : Finset (Fin 33) :=
  Finset.univ.filter fun x =>
    colorInterval x ⊆ wordFiber w b

theorem fiberPositions_eq_wordFiber
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11) :
    fiberPositions c b = wordFiber (blockLabel c hc) b := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ :=
      ((chosenFiberBlocks c hc b).covers t).mp ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    refine ⟨blockStart c hc (b, i), ?_, hi⟩
    change
      (blockAt c hc (blockStart c hc (b, i))).1 = b
    rw [blockAt_of_start]
  · intro ht
    rcases (Finset.mem_filter.mp ht).2 with ⟨s, hsb, hts⟩
    have hblock :
        t ∈ colorInterval
          (blockStart c hc (blockAt c hc s)) := by
      rw [blockAt_start]
      exact hts
    have hf :
        t ∈ fiberPositions c (blockAt c hc s).1 :=
      ((chosenFiberBlocks c hc (blockAt c hc s).1).covers t).mpr
        ⟨(blockAt c hc s).2, hblock⟩
    change t ∈ fiberPositions c (blockLabel c hc s) at hf
    rw [hsb] at hf
    exact hf

theorem fiberPositions_eq_candidateFiber
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (w : Fin 33 → Fin 11)
    (hw : ∀ t, blockLabel c hc t = w t)
    (b : Fin 11) :
    fiberPositions c b = wordFiber w b := by
  have hfun : blockLabel c hc = w := funext hw
  rw [fiberPositions_eq_wordFiber c hc b, hfun]

theorem vertex_interval_subset_fiber
    (c : Vertex → Fin 33)
    (a : Fin 5)
    (b : Fin 11) :
    colorInterval (c (a, b)) ⊆ fiberPositions c b := by
  intro t ht
  exact Finset.mem_biUnion.mpr
    ⟨a, Finset.mem_univ a, ht⟩

theorem coloring_uses_allowedColors
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (w : Fin 33 → Fin 11)
    (hw : ∀ t, blockLabel c hc t = w t)
    (a : Fin 5)
    (b : Fin 11) :
    c (a, b) ∈ allowedColors w b := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← fiberPositions_eq_candidateFiber c hc w hw b]
  exact vertex_interval_subset_fiber c a b

theorem coloring_covers_candidateFiber
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (w : Fin 33 → Fin 11)
    (hw : ∀ t, blockLabel c hc t = w t)
    (b : Fin 11)
    (t : Fin 33)
    (ht : t ∈ wordFiber w b) :
    ∃ a : Fin 5, t ∈ colorInterval (c (a, b)) := by
  rw [← fiberPositions_eq_candidateFiber c hc w hw b] at ht
  rcases Finset.mem_biUnion.mp ht with ⟨a, _, ha⟩
  exact ⟨a, ha⟩

end CircularColoring

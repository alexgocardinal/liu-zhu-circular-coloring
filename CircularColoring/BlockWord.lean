import CircularColoring.UniqueStarts

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

noncomputable def blockAt
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : Block :=
  Classical.choose ((unique_block_start c hc t).exists)

theorem blockAt_start
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    blockStart c hc (blockAt c hc t) = t :=
  Classical.choose_spec ((unique_block_start c hc t).exists)

theorem blockAt_of_start
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (q : Block) :
    blockAt c hc (blockStart c hc q) = q := by
  obtain ⟨r, hr, hunique⟩ :=
    unique_block_start c hc (blockStart c hc q)
  have hchosen := blockAt_start c hc (blockStart c hc q)
  exact (hunique _ hchosen).trans (hunique q rfl).symm

noncomputable def blockLabel
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : Fin 11 :=
  (blockAt c hc t).1

noncomputable def labelPositions
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11) : Finset (Fin 33) :=
  Finset.univ.filter fun t => blockLabel c hc t = b

theorem labelPositions_card_eq_three
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11) :
    (labelPositions c hc b).card = 3 := by
  have hcard :
      (labelPositions c hc b).card =
      (Finset.univ : Finset (Fin 3)).card := by
    apply Finset.card_bij
      (fun (t : Fin 33) _ => (blockAt c hc t).2)

    · intro t _
      exact Finset.mem_univ _

    · intro t ht s hs heq
      have ht' : (blockAt c hc t).1 = b :=
        (Finset.mem_filter.mp ht).2
      have hs' : (blockAt c hc s).1 = b :=
        (Finset.mem_filter.mp hs).2
      have hblocks : blockAt c hc t = blockAt c hc s :=
        Prod.ext (ht'.trans hs'.symm) heq
      have hstarts := congrArg (blockStart c hc) hblocks
      simpa only [blockAt_start] using hstarts

    · intro i _
      refine ⟨blockStart c hc (b, i), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change
          (blockAt c hc (blockStart c hc (b, i))).1 = b
        rw [blockAt_of_start]
      · rw [blockAt_of_start]

  exact hcard.trans (by decide)

end CircularColoring

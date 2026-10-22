import CircularColoring.Blocks

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

noncomputable def occupiedBlocks
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : Finset Block :=
  Finset.univ.filter fun q =>
    t ∈ colorInterval (blockStart c hc q)

theorem occupiedBlocks_card_eq_four
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    (occupiedBlocks c hc t).card = 4 := by
  have hcard :
      (occupiedBlocks c hc t).card =
      (activeFibers c t).card := by
    apply Finset.card_bij (fun (q : Block) _ => q.1)

    · intro q hq
      have hmem :
          t ∈ colorInterval (blockStart c hc q) :=
        (Finset.mem_filter.mp hq).2
      have hf : t ∈ fiberPositions c q.1 :=
        ((chosenFiberBlocks c hc q.1).covers t).mpr
          ⟨q.2, hmem⟩
      exact (mem_fiber_iff_active c q.1 t).mp hf

    · intro q hq r hr heq
      rcases q with ⟨b, i⟩
      rcases r with ⟨d, j⟩
      change b = d at heq
      subst d
      have hi :
          t ∈ colorInterval (blockStart c hc (b, i)) :=
        (Finset.mem_filter.mp hq).2
      have hj :
          t ∈ colorInterval (blockStart c hc (b, j)) :=
        (Finset.mem_filter.mp hr).2
      have hij : i = j := by
        by_contra h
        have hdis :=
          (chosenFiberBlocks c hc b).disjoint i j h
        exact Finset.disjoint_left.mp hdis hi hj
      exact Prod.ext rfl hij

    · intro b hb
      have ht : t ∈ fiberPositions c b :=
        (mem_fiber_iff_active c b t).mpr hb
      obtain ⟨i, hi, _⟩ :=
        unique_block_in_active_fiber c hc b t ht
      refine ⟨(b, i), ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ (b, i), hi⟩

  exact hcard.trans (activeFibers_card_eq_four c hc t)

end CircularColoring

import CircularColoring.BlockCoverage

namespace CircularColoring

open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def previousSlot (t : Fin 33) : Fin 33 :=
  ⟨(t.val + 32) % 33, Nat.mod_lt _ (by decide)⟩

def backFour (t : Fin 33) : Fin 33 :=
  ⟨(t.val + 29) % 33, Nat.mod_lt _ (by decide)⟩

theorem interval_step_identity :
    ∀ s t : Fin 33,
      (if t ∈ colorInterval s then (1 : Nat) else 0) +
        (if s = backFour t then 1 else 0) =
      (if previousSlot t ∈ colorInterval s then 1 else 0) +
        (if s = t then 1 else 0) := by
  decide

noncomputable def coverCount
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : Nat :=
  ∑ q : Block,
    if t ∈ colorInterval (blockStart c hc q) then 1 else 0

noncomputable def startCount
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) : Nat :=
  ∑ q : Block,
    if blockStart c hc q = t then 1 else 0

theorem coverCount_eq_four
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    coverCount c hc t = 4 := by
  unfold coverCount
  have h := occupiedBlocks_card_eq_four c hc t
  simpa only [occupiedBlocks,
    Finset.card_eq_sum_ones, Finset.sum_filter] using h

theorem startCount_backFour
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    startCount c hc t = startCount c hc (backFour t) := by
  have hsum :
      (∑ q : Block,
        ((if t ∈ colorInterval (blockStart c hc q)
            then (1 : Nat) else 0) +
         (if blockStart c hc q = backFour t then 1 else 0))) =
      (∑ q : Block,
        ((if previousSlot t ∈ colorInterval (blockStart c hc q)
            then (1 : Nat) else 0) +
         (if blockStart c hc q = t then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro q _
    exact interval_step_identity (blockStart c hc q) t

  simp only [Finset.sum_add_distrib] at hsum
  change
    coverCount c hc t + startCount c hc (backFour t) =
    coverCount c hc (previousSlot t) + startCount c hc t
    at hsum
  simp only [coverCount_eq_four] at hsum
  omega

end CircularColoring

import CircularColoring.StartRecurrence

namespace CircularColoring

open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def backFourOrbit : Nat → Fin 33
  | 0 => 0
  | n + 1 => backFour (backFourOrbit n)

theorem backFourOrbit_covers :
    ∀ t : Fin 33, ∃ n : Fin 33,
      backFourOrbit n.val = t := by
  decide

theorem four_step_constant
    (f : Fin 33 → Nat)
    (hf : ∀ t, f t = f (backFour t)) :
    ∀ t, f t = f 0 := by
  have hiter : ∀ n : Nat, f (backFourOrbit n) = f 0 := by
    intro n
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        change f (backFour (backFourOrbit n)) = f 0
        exact (hf (backFourOrbit n)).symm.trans ih
  intro t
  obtain ⟨n, hn⟩ := backFourOrbit_covers t
  rw [← hn]
  exact hiter n.val

theorem interval_at_zero_identity :
    ∀ s : Fin 33,
      (if (0 : Fin 33) ∈ colorInterval s then (1 : Nat) else 0) =
      (if s = 0 then 1 else 0) +
      (if s = 32 then 1 else 0) +
      (if s = 31 then 1 else 0) +
      (if s = 30 then 1 else 0) := by
  decide

theorem startCount_eq_one
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    startCount c hc t = 1 := by
  have hconst :=
    four_step_constant (startCount c hc) (startCount_backFour c hc)

  have hsum :
      (∑ q : Block,
        if (0 : Fin 33) ∈ colorInterval (blockStart c hc q)
          then (1 : Nat) else 0) =
      (∑ q : Block,
        ((if blockStart c hc q = 0 then (1 : Nat) else 0) +
         (if blockStart c hc q = 32 then 1 else 0) +
         (if blockStart c hc q = 31 then 1 else 0) +
         (if blockStart c hc q = 30 then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro q _
    exact interval_at_zero_identity (blockStart c hc q)

  simp only [Finset.sum_add_distrib] at hsum
  change coverCount c hc 0 =
    startCount c hc 0 + startCount c hc 32 +
    startCount c hc 31 + startCount c hc 30 at hsum
  rw [coverCount_eq_four c hc 0] at hsum
  have h32 := hconst 32
  have h31 := hconst 31
  have h30 := hconst 30
  have ht := hconst t
  omega

theorem unique_block_start
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (t : Fin 33) :
    ∃! q : Block, blockStart c hc q = t := by
  let s : Finset Block :=
    Finset.univ.filter fun q => blockStart c hc q = t

  have hcard : s.card = 1 := by
    have h := startCount_eq_one c hc t
    simpa only [s, startCount,
      Finset.card_eq_sum_ones, Finset.sum_filter] using h

  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  have hqmem : q ∈ s := by
    rw [hq]
    simp
  have hstart : blockStart c hc q = t :=
    (Finset.mem_filter.mp hqmem).2

  refine ⟨q, hstart, ?_⟩
  intro r hr
  have hrmem : r ∈ s :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
  rw [hq] at hrmem
  exact Finset.mem_singleton.mp hrmem

end CircularColoring

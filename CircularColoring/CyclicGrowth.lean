import CircularColoring.FastRowColors

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def expandOnce (A : Finset (Fin 33)) : Finset (Fin 33) :=
  A ∪ A.image nextSlot

def expandTimes : Nat → Finset (Fin 33) → Finset (Fin 33)
  | 0, A => A
  | n + 1, A => expandOnce (expandTimes n A)

theorem advanceSlot_covers :
    ∀ s t : Fin 33,
      ∃ n : Fin 33, advanceSlot s n.val = t := by
  decide

theorem next_closed_set_is_univ
    (A : Finset (Fin 33))
    (hne : A.Nonempty)
    (hclosed : ∀ x ∈ A, nextSlot x ∈ A) :
    A = Finset.univ := by
  obtain ⟨s, hs⟩ := hne
  have hiter :
      ∀ n : Nat, n ≤ 33 → advanceSlot s n ∈ A := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [advanceSlot_zero]
        exact hs
    | succ n ih =>
        intro hn
        have hnlt : n < 33 := by omega
        rw [← advanceSlot_step s ⟨n, hnlt⟩]
        exact hclosed _ (ih (by omega))
  ext t
  constructor
  · intro _
    exact Finset.mem_univ t
  · intro _
    obtain ⟨n, hn⟩ := advanceSlot_covers s t
    rw [← hn]
    exact hiter n.val (by omega)

theorem subset_expandOnce (A : Finset (Fin 33)) :
    A ⊆ expandOnce A := by
  intro x hx
  exact Finset.mem_union.mpr (Or.inl hx)

theorem expandOnce_nonempty
    (A : Finset (Fin 33))
    (hne : A.Nonempty) :
    (expandOnce A).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, subset_expandOnce A hx⟩

theorem expandOnce_grows
    (A : Finset (Fin 33))
    (hne : A.Nonempty)
    (hsmall : A.card < 33) :
    A.card + 1 ≤ (expandOnce A).card := by
  by_contra h
  have hcard : (expandOnce A).card ≤ A.card := by omega
  have heq : A = expandOnce A :=
    Finset.eq_of_subset_of_card_le (subset_expandOnce A) hcard
  have hclosed : ∀ x ∈ A, nextSlot x ∈ A := by
    intro x hx
    have hnext : nextSlot x ∈ expandOnce A :=
      Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    rw [← heq] at hnext
    exact hnext
  have huniv := next_closed_set_is_univ A hne hclosed
  have hsize : A.card = 33 := by
    rw [huniv]
    decide
  omega

theorem expandOnce_card_bound
    (A : Finset (Fin 33))
    (hne : A.Nonempty) :
    min 33 (A.card + 1) ≤ (expandOnce A).card := by
  by_cases hsmall : A.card < 33
  · have h := expandOnce_grows A hne hsmall
    omega
  · have h := Finset.card_le_card (subset_expandOnce A)
    omega

theorem expandTimes_nonempty
    (n : Nat)
    (A : Finset (Fin 33))
    (hne : A.Nonempty) :
    (expandTimes n A).Nonempty := by
  induction n with
  | zero => exact hne
  | succ n ih => exact expandOnce_nonempty _ ih

theorem expandTimes_card_bound
    (n : Nat)
    (A : Finset (Fin 33))
    (hne : A.Nonempty) :
    min 33 (A.card + n) ≤ (expandTimes n A).card := by
  induction n with
  | zero =>
      change min 33 (A.card + 0) ≤ A.card
      omega
  | succ n ih =>
      have h := expandOnce_card_bound
        (expandTimes n A) (expandTimes_nonempty n A hne)
      change min 33 (A.card + (n + 1)) ≤
        (expandOnce (expandTimes n A)).card
      omega

theorem eleven_positions_expand_to_fourteen
    (A : Finset (Fin 33))
    (hcard : A.card = 11) :
    14 ≤ (expandTimes 3 A).card := by
  have hne : A.Nonempty :=
    Finset.card_pos.mp (by omega)
  have h := expandTimes_card_bound 3 A hne
  rw [hcard] at h
  norm_num at h
  exact h

end CircularColoring

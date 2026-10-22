import CircularColoring.ExcludeFast

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def slowFiberOrigin (k : Fin 24) : Fin 33 :=
  match k.val with
  | 5 => 22
  | 7 => 23
  | 9 => 0
  | 14 => 24
  | 16 => 32
  | 18 => 31
  | _ => 0

def slowFiberStart (initial : FiniteState) (b : Fin 11) : Fin 33 :=
  let relative := (b.val + 11 - initial.1.val) % 11
  shiftColor (slowFiberOrigin initial.2)
    (if orderClass initial.2 = 0 then 30 * relative
      else 3 * relative)

-- Each label has three block starts, spaced four positions apart.
theorem slow_candidate_positions :
    ∀ initial : FiniteState,
      (initial.2 = 5 ∨ initial.2 = 7 ∨ initial.2 = 9 ∨
        initial.2 = 14 ∨ initial.2 = 16 ∨ initial.2 = 18) →
      ∀ (b : Fin 11) (t : Fin 33),
        candidateWord slowSuccessor initial t = b ↔
          (t = slowFiberStart initial b ∨
            t = shiftColor (slowFiberStart initial b) 4 ∨
            t = shiftColor (slowFiberStart initial b) 8) := by
  decide

theorem wordFiber_eq_three_blocks
    (w : Fin 33 → Fin 11)
    (b : Fin 11)
    (p q r : Fin 33)
    (hpositions : ∀ s : Fin 33,
      w s = b ↔ (s = p ∨ s = q ∨ s = r)) :
    wordFiber w b =
      (colorInterval p ∪ colorInterval q) ∪ colorInterval r := by
  ext t
  constructor
  · intro ht
    rcases (Finset.mem_filter.mp ht).2 with ⟨s, hsb, hts⟩
    rcases (hpositions s).mp hsb with hs | hs | hs
    · subst s
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl hts)))
    · subst s
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr hts)))
    · subst s
      exact Finset.mem_union.mpr (Or.inr hts)
  · intro ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact ⟨p, (hpositions p).mpr (Or.inl rfl), ht⟩
      · exact ⟨q, (hpositions q).mpr (Or.inr (Or.inl rfl)), ht⟩
    · exact ⟨r, (hpositions r).mpr (Or.inr (Or.inr rfl)), ht⟩

theorem slow_candidate_fiber
    (initial : FiniteState)
    (hinitial :
      initial.2 = 5 ∨ initial.2 = 7 ∨ initial.2 = 9 ∨
      initial.2 = 14 ∨ initial.2 = 16 ∨ initial.2 = 18)
    (b : Fin 11) :
    wordFiber (candidateWord slowSuccessor initial) b =
      consecutiveFiber (slowFiberStart initial b) := by
  exact wordFiber_eq_three_blocks
    (candidateWord slowSuccessor initial) b
    (slowFiberStart initial b)
    (shiftColor (slowFiberStart initial b) 4)
    (shiftColor (slowFiberStart initial b) 8)
    (slow_candidate_positions initial hinitial b)

theorem slow_candidate_vertex_placements
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (initial : FiniteState)
    (hinitial :
      initial.2 = 5 ∨ initial.2 = 7 ∨ initial.2 = 9 ∨
      initial.2 = 14 ∨ initial.2 = 16 ∨ initial.2 = 18)
    (hw : ∀ t, blockLabel c hc t =
      candidateWord slowSuccessor initial t)
    (a : Fin 5)
    (b : Fin 11) :
    ((c (a, b)).val + 33 -
      (slowFiberStart initial b).val) % 33 ≤ 8 := by
  have hallowed := coloring_uses_allowedColors c hc
    (candidateWord slowSuccessor initial) hw a b
  have hsub := (Finset.mem_filter.mp hallowed).2
  rw [slow_candidate_fiber initial hinitial b] at hsub
  exact
    (interval_inside_consecutiveFiber
      (slowFiberStart initial b) (c (a, b))).mp hsub

end CircularColoring

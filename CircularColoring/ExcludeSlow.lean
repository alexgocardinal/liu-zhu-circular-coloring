import CircularColoring.LocalSegments

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- Every remaining candidate contains the three required fiber locations.
theorem slow_candidate_three_starts :
    ∀ initial : FiniteState,
      (initial.2 = 5 ∨ initial.2 = 7 ∨ initial.2 = 9 ∨
        initial.2 = 14 ∨ initial.2 = 16 ∨ initial.2 = 18) →
      ∃ b1 b2 : Fin 11,
        slowFiberStart initial b1 =
          shiftColor (slowFiberStart initial 0) 3 ∧
        slowFiberStart initial b2 =
          shiftColor (slowFiberStart initial 0) 6 := by
  decide

theorem no_slow_candidate
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (initial : FiniteState)
    (hinitial :
      initial.2 = 5 ∨ initial.2 = 7 ∨ initial.2 = 9 ∨
      initial.2 = 14 ∨ initial.2 = 16 ∨ initial.2 = 18)
    (hw : ∀ t, blockLabel c hc t =
      candidateWord slowSuccessor initial t) :
    False := by
  obtain ⟨b1, b2, hstart1, hstart2⟩ :=
    slow_candidate_three_starts initial hinitial

  have h0 : ∀ a : Fin 5,
      (rotateColor (c (a, 0)) (slowFiberStart initial 0)).val ≤ 8 := by
    intro a
    exact slow_candidate_vertex_placements
      c hc initial hinitial hw a 0

  have h1 : ∀ a : Fin 5,
      (rotateColor (c (a, b1))
        (shiftColor (slowFiberStart initial 0) 3)).val ≤ 8 := by
    intro a
    have hb := slow_candidate_vertex_placements
      c hc initial hinitial hw a b1
    change
      (rotateColor (c (a, b1)) (slowFiberStart initial b1)).val ≤ 8
      at hb
    rw [hstart1] at hb
    exact hb

  have h2 : ∀ a : Fin 5,
      (rotateColor (c (a, b2))
        (shiftColor (slowFiberStart initial 0) 6)).val ≤ 8 := by
    intro a
    have hb := slow_candidate_vertex_placements
      c hc initial hinitial hw a b2
    change
      (rotateColor (c (a, b2)) (slowFiberStart initial b2)).val ≤ 8
      at hb
    rw [hstart2] at hb
    exact hb

  exact no_three_close_fibers c hc 0 b1 b2
    (slowFiberStart initial 0) h0 h1 h2

-- The fixed 55-vertex graph has no (33,4)-coloring.
theorem no_coloring33_4 :
    ¬ ∃ c : Vertex → Fin 33, IsColoring33_4 c := by
  rintro ⟨c, hc⟩
  rcases coloring_candidate_words c hc with
    ⟨initial, hinitial, hw⟩ | ⟨initial, hinitial, hw⟩
  · exact no_fast_candidate c hc initial hinitial hw
  · exact no_slow_candidate c hc initial hinitial hw

end CircularColoring

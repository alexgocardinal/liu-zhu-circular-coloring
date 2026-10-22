import CircularColoring.FastFibers

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem label_of_interval_subset_spaced
    (w : Fin 33 → Fin 11)
    (b : Fin 11)
    (p x : Fin 33)
    (hpositions : ∀ s : Fin 33,
      w s = b ↔
        (s = p ∨ s = shiftColor p 11 ∨ s = shiftColor p 22))
    (hsub : colorInterval x ⊆ wordFiber w b) :
    w x = b := by
  rw [wordFiber_eq_spacedFiber w b p hpositions] at hsub
  exact (hpositions x).mpr
    ((interval_inside_spacedFiber p x).mp hsub)

theorem fast_allowed_color_has_label
    (initial : FiniteState)
    (hinitial : initial.2 = 0 ∨ initial.2 = 23)
    (b : Fin 11)
    (x : Fin 33)
    (hx : x ∈ allowedColors
      (candidateWord fastSuccessor initial) b) :
    candidateWord fastSuccessor initial x = b := by
  have hsub := (Finset.mem_filter.mp hx).2
  rcases initial with ⟨a, k⟩
  rcases hinitial with h | h
  · change k = 0 at h
    subst k
    exact label_of_interval_subset_spaced
      (candidateWord fastSuccessor (a, 0)) b
      (forwardFiberStart a b) x
      (fast_forward_positions a b) hsub
  · change k = 23 at h
    subst k
    exact label_of_interval_subset_spaced
      (candidateWord fastSuccessor (a, 23)) b
      (backwardFiberStart a b) x
      (fast_backward_positions a b) hsub

theorem fast_vertex_color_has_label
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (initial : FiniteState)
    (hinitial : initial.2 = 0 ∨ initial.2 = 23)
    (hw : ∀ t, blockLabel c hc t =
      candidateWord fastSuccessor initial t)
    (a : Fin 5)
    (b : Fin 11) :
    candidateWord fastSuccessor initial (c (a, b)) = b := by
  exact fast_allowed_color_has_label initial hinitial b (c (a, b))
    (coloring_uses_allowedColors c hc
      (candidateWord fastSuccessor initial) hw a b)

theorem fast_row_colors_injective
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (initial : FiniteState)
    (hinitial : initial.2 = 0 ∨ initial.2 = 23)
    (hw : ∀ t, blockLabel c hc t =
      candidateWord fastSuccessor initial t)
    (a : Fin 5) :
    Function.Injective (fun b : Fin 11 => c (a, b)) := by
  intro b d hbd
  change c (a, b) = c (a, d) at hbd
  have hb :=
    fast_vertex_color_has_label c hc initial hinitial hw a b
  have hd :=
    fast_vertex_color_has_label c hc initial hinitial hw a d
  rw [hbd] at hb
  exact hb.symm.trans hd

def rowColors
    (c : Vertex → Fin 33)
    (a : Fin 5) : Finset (Fin 33) :=
  Finset.univ.image (fun b : Fin 11 => c (a, b))

theorem fast_rowColors_card
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (initial : FiniteState)
    (hinitial : initial.2 = 0 ∨ initial.2 = 23)
    (hw : ∀ t, blockLabel c hc t =
      candidateWord fastSuccessor initial t)
    (a : Fin 5) :
    (rowColors c a).card = 11 := by
  have hinj :
      Set.InjOn (fun b : Fin 11 => c (a, b))
        (Finset.univ : Finset (Fin 11)) := by
    intro b _ d _ hbd
    exact fast_row_colors_injective c hc initial hinitial hw a hbd
  have hcard := Finset.card_image_of_injOn hinj
  change
    (Finset.univ.image (fun b : Fin 11 => c (a, b))).card = 11
  simpa using hcard

end CircularColoring

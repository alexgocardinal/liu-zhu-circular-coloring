import CircularColoring.SegmentObstruction

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

-- Express a color relative to a nearby fiber's starting position.
theorem rotate_shift_offset :
    ∀ (p x : Fin 33) (d : Fin 7),
      (rotateColor x (shiftColor p d.val)).val ≤ 8 →
      (rotateColor x p).val =
        d.val + (rotateColor x (shiftColor p d.val)).val := by
  decide

theorem shift_three_twice :
    ∀ p : Fin 33,
      shiftColor (shiftColor p 3) 3 = shiftColor p 6 := by
  decide

def localSegment
    (c : Vertex → Fin 33)
    (b : Fin 11)
    (p : Fin 33)
    (hbound : ∀ a : Fin 5, (rotateColor (c (a, b)) p).val ≤ 8) :
    Fin 5 → Fin 9 :=
  fun a =>
    ⟨(rotateColor (c (a, b)) p).val,
      Nat.lt_succ_of_le (hbound a)⟩

theorem localSegment_valid
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b : Fin 11)
    (p : Fin 33)
    (hbound : ∀ a : Fin 5, (rotateColor (c (a, b)) p).val ≤ 8) :
    IsSegmentColoring (localSegment c b p hbound) := by
  intro i j hij
  have hedge := hc (i, b) (j, b) (Or.inl hij)
  rw [← rotation_preserves_distance
    (c (i, b)) (c (j, b)) p] at hedge
  exact hedge

theorem local_segments_compatible
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b e : Fin 11)
    (p q : Fin 33)
    (d : Fin 7)
    (hp : ∀ a : Fin 5, (rotateColor (c (a, b)) p).val ≤ 8)
    (hq : ∀ a : Fin 5, (rotateColor (c (a, e)) q).val ≤ 8)
    (hshift : q = shiftColor p d.val) :
    SegmentsCompatible d.val
      (localSegment c b p hp) (localSegment c e q hq) := by
  subst q
  intro i j hij
  have hedge := hc (i, b) (j, e) (Or.inl hij)
  rw [← rotation_preserves_distance
    (c (i, b)) (c (j, e)) p] at hedge
  have hoffset := rotate_shift_offset p (c (j, e)) d (hq j)
  rw [hoffset] at hedge
  exact hedge

theorem no_three_close_fibers
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c)
    (b0 b1 b2 : Fin 11)
    (p : Fin 33)
    (h0 : ∀ a : Fin 5,
      (rotateColor (c (a, b0)) p).val ≤ 8)
    (h1 : ∀ a : Fin 5,
      (rotateColor (c (a, b1)) (shiftColor p 3)).val ≤ 8)
    (h2 : ∀ a : Fin 5,
      (rotateColor (c (a, b2)) (shiftColor p 6)).val ≤ 8) :
    False := by
  let f := localSegment c b0 p h0
  let g := localSegment c b1 (shiftColor p 3) h1
  let h := localSegment c b2 (shiftColor p 6) h2

  have hfg : SegmentsCompatible 3 f g :=
    local_segments_compatible c hc b0 b1
      p (shiftColor p 3) ⟨3, by decide⟩ h0 h1 rfl

  have hgh : SegmentsCompatible 3 g h :=
    local_segments_compatible c hc b1 b2
      (shiftColor p 3) (shiftColor p 6)
      ⟨3, by decide⟩ h1 h2 (shift_three_twice p).symm

  have hfh : SegmentsCompatible 6 f h :=
    local_segments_compatible c hc b0 b2
      p (shiftColor p 6) ⟨6, by decide⟩ h0 h2 rfl

  exact no_three_segment_colorings f g h
    (localSegment_valid c hc b0 p h0)
    (localSegment_valid c hc b1 (shiftColor p 3) h1)
    (localSegment_valid c hc b2 (shiftColor p 6) h2)
    hfg hgh hfh

end CircularColoring

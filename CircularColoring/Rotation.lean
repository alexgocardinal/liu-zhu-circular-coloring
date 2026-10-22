import CircularColoring.Fibers

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def rotateColor (x origin : Fin 33) : Fin 33 :=
  ⟨(x.val + 33 - origin.val) % 33,
    Nat.mod_lt _ (by decide)⟩

theorem rotateColor_self (x : Fin 33) :
    rotateColor x x = 0 := by
  apply Fin.ext
  dsimp [rotateColor]
  omega

theorem rotation_preserves_distance
    (x y origin : Fin 33) :
    circularDistance 33
      (rotateColor x origin).val
      (rotateColor y origin).val =
    circularDistance 33 x.val y.val := by
  revert x y origin
  decide

def normalizeColoring (c : Vertex → Fin 33) :
    Vertex → Fin 33 :=
  fun v => rotateColor (c v) (c (0, 0))

theorem normalized_origin (c : Vertex → Fin 33) :
    normalizeColoring c (0, 0) = 0 := by
  exact rotateColor_self (c (0, 0))

theorem normalization_preserves_coloring
    (c : Vertex → Fin 33)
    (hc : IsColoring33_4 c) :
    IsColoring33_4 (normalizeColoring c) := by
  intro u v huv
  change 4 ≤ circularDistance 33
    (rotateColor (c u) (c (0, 0))).val
    (rotateColor (c v) (c (0, 0))).val
  rw [rotation_preserves_distance]
  exact hc u v huv

end CircularColoring

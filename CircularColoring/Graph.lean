import Std

namespace CircularColoring

-- A vertex is a pair: one number from 0 to 4,
-- and one number from 0 to 10.
abbrev Vertex := Fin 5 × Fin 11

-- Distance around a circle with n positions.
def circularDistance (n a b : Nat) : Nat :=
  min ((a + n - b) % n) ((b + n - a) % n)

-- The adjacency rule for K_(5/2) OR K_(11/4).
def Adj (u v : Vertex) : Prop :=
  circularDistance 5 u.1.val v.1.val ≥ 2 ∨
  circularDistance 11 u.2.val v.2.val ≥ 4

instance (u v : Vertex) : Decidable (Adj u v) := by
  unfold Adj
  infer_instance

set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- No vertex is adjacent to itself.
theorem no_loops :
    ∀ (a : Fin 5) (b : Fin 11),
      ¬ Adj (a, b) (a, b) := by
  decide

-- Adjacency works in both directions.
theorem adjacency_symmetric :
    ∀ (a c : Fin 5) (b d : Fin 11),
      Adj (a, b) (c, d) ↔ Adj (c, d) (a, b) := by
  decide

end CircularColoring

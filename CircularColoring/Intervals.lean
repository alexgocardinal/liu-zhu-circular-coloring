import Mathlib
import CircularColoring.Graph

namespace CircularColoring

-- The four consecutive positions starting at color x.
def colorInterval (x : Fin 33) : Finset (Fin 33) :=
  Finset.univ.filter fun t =>
    (t.val + 33 - x.val) % 33 < 4

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem colorInterval_card :
    ∀ x : Fin 33, (colorInterval x).card = 4 := by
  decide

theorem colorIntervals_disjoint
    (x y : Fin 33)
    (h : 4 ≤ circularDistance 33 x.val y.val) :
    Disjoint (colorInterval x) (colorInterval y) := by
  rw [Finset.disjoint_left]
  intro t ht ht'
  have hx : (t.val + 33 - x.val) % 33 < 4 :=
    (Finset.mem_filter.mp ht).2
  have hy : (t.val + 33 - y.val) % 33 < 4 :=
    (Finset.mem_filter.mp ht').2
  unfold circularDistance at h
  omega

end CircularColoring

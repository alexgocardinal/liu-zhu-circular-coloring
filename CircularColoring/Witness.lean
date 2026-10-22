import CircularColoring.Graph

namespace CircularColoring

def witnessTable : List (List Nat) :=
  [ [0, 0, 11, 11, 11, 11, 6, 6, 6, 0, 0],
    [16, 15, 15, 10, 10, 10, 5, 5, 5, 5, 16],
    [15, 15, 14, 14, 9, 9, 9, 4, 4, 4, 3],
    [2, 13, 13, 13, 13, 8, 8, 8, 3, 3, 3],
    [1, 1, 12, 12, 12, 7, 7, 7, 7, 1, 1] ]

def witness (v : Vertex) : Nat :=
  (witnessTable.getD v.1.val []).getD v.2.val 0

set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- Every assigned color lies between 0 and 16.
theorem witness_in_range :
    ∀ (a : Fin 5) (b : Fin 11),
      witness (a, b) < 17 := by
  decide

-- Every edge has circular color distance at least 2.
theorem witness_respects_edges :
    ∀ (a c : Fin 5) (b d : Fin 11),
      Adj (a, b) (c, d) →
      circularDistance 17
        (witness (a, b)) (witness (c, d)) ≥ 2 := by
  decide

end CircularColoring

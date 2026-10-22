import CircularColoring.ExcludeSlow

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- The standard circular complete graph K_(p/q).
def circularComplete (p q : Nat) : SimpleGraph (Fin p) where
  Adj x y :=
    x ≠ y ∧ q ≤ circularDistance p x.val y.val
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    simpa only [circularDistance, Nat.min_comm] using h.2⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

-- The Cartesian sum, also called the OR product.
def cartesianSumGraph
    {V W : Type}
    (G : SimpleGraph V)
    (H : SimpleGraph W) : SimpleGraph (V × W) where
  Adj u v := G.Adj u.1 v.1 ∨ H.Adj u.2 v.2
  symm := ⟨by
    intro u v h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm⟩
  loopless := ⟨by
    intro u h
    rcases h with h | h
    · exact G.irrefl h
    · exact H.irrefl h⟩

def counterexampleGraph : SimpleGraph Vertex :=
  cartesianSumGraph (circularComplete 5 2) (circularComplete 11 4)

theorem first_factor_adjacency :
    ∀ x y : Fin 5,
      (x ≠ y ∧ 2 ≤ circularDistance 5 x.val y.val) ↔
        2 ≤ circularDistance 5 x.val y.val := by
  decide

theorem second_factor_adjacency :
    ∀ x y : Fin 11,
      (x ≠ y ∧ 4 ≤ circularDistance 11 x.val y.val) ↔
        4 ≤ circularDistance 11 x.val y.val := by
  decide

-- The Mathlib graph has exactly our previously verified adjacency rule.
theorem counterexampleGraph_adjacency
    (u v : Vertex) :
    counterexampleGraph.Adj u v ↔ Adj u v := by
  change
    ((u.1 ≠ v.1 ∧
        2 ≤ circularDistance 5 u.1.val v.1.val) ∨
      (u.2 ≠ v.2 ∧
        4 ≤ circularDistance 11 u.2.val v.2.val)) ↔
    (2 ≤ circularDistance 5 u.1.val v.1.val ∨
      4 ≤ circularDistance 11 u.2.val v.2.val)
  rw [first_factor_adjacency, second_factor_adjacency]

-- State the obstruction using Mathlib graph homomorphisms.
theorem no_hom_to_circularComplete33_4 :
    ¬ Nonempty (counterexampleGraph →g circularComplete 33 4) := by
  rintro ⟨f⟩
  apply no_coloring33_4
  refine ⟨fun v => f v, ?_⟩
  intro u v huv
  have hgraph : counterexampleGraph.Adj u v :=
    (counterexampleGraph_adjacency u v).mpr huv
  have htarget := f.map_adj hgraph
  exact htarget.2

end CircularColoring

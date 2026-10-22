import CircularColoring.CandidateFibers

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def shiftColor (p : Fin 33) (k : Nat) : Fin 33 :=
  ⟨(p.val + k) % 33, Nat.mod_lt _ (by decide)⟩

-- Three separated four-position intervals.
def spacedFiber (p : Fin 33) : Finset (Fin 33) :=
  (colorInterval p ∪ colorInterval (shiftColor p 11)) ∪
    colorInterval (shiftColor p 22)

-- Three adjoining four-position intervals.
def consecutiveFiber (p : Fin 33) : Finset (Fin 33) :=
  (colorInterval p ∪ colorInterval (shiftColor p 4)) ∪
    colorInterval (shiftColor p 8)

-- In the separated case, an interval must coincide with a block.
theorem interval_inside_spacedFiber :
    ∀ p x : Fin 33,
      (colorInterval x ⊆ spacedFiber p) ↔
        (x = p ∨ x = shiftColor p 11 ∨
          x = shiftColor p 22) := by
  decide

-- In the adjoining case, there are exactly nine possible starts.
theorem interval_inside_consecutiveFiber :
    ∀ p x : Fin 33,
      (colorInterval x ⊆ consecutiveFiber p) ↔
        (x.val + 33 - p.val) % 33 ≤ 8 := by
  decide

-- Assigning the five first coordinates to three separated blocks.
def IsFiveCycleLabeling (f : Fin 5 → Fin 3) : Prop :=
  ∀ i j : Fin 5,
    2 ≤ circularDistance 5 i.val j.val → f i ≠ f j

def binSize (f : Fin 5 → Fin 3) (k : Fin 3) : Nat :=
  (Finset.univ.filter fun i => f i = k).card

-- Every proper assignment has block sizes 2, 2, 1.
theorem five_cycle_three_bin_sizes :
    ∀ f : Fin 5 → Fin 3,
      IsFiveCycleLabeling f →
      (∀ k : Fin 3, 1 ≤ binSize f k ∧ binSize f k ≤ 2) ∧
      (∃! k : Fin 3, binSize f k = 1) := by
  unfold ExistsUnique IsFiveCycleLabeling
  decide

end CircularColoring

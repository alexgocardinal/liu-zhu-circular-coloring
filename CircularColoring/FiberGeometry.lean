import CircularColoring.Rotation

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

-- Normalize the first color to zero.
-- The five required edges force at least one extra separated pair.
theorem extra_separated_pair_at_zero :
    ∀ (x1 x2 x3 x4 : Fin 33),
      4 ≤ circularDistance 33 0 x2.val →
      4 ≤ circularDistance 33 0 x3.val →
      4 ≤ circularDistance 33 x1.val x3.val →
      4 ≤ circularDistance 33 x1.val x4.val →
      4 ≤ circularDistance 33 x2.val x4.val →
      (4 ≤ circularDistance 33 0 x1.val ∨
       4 ≤ circularDistance 33 x1.val x2.val ∨
       4 ≤ circularDistance 33 x2.val x3.val ∨
       4 ≤ circularDistance 33 x3.val x4.val ∨
       4 ≤ circularDistance 33 x4.val 0) := by
  intro x1 x2 x3 x4 h02 h03 _ h14 _
  by_contra hnone
  simp only [not_or, not_le] at hnone
  rcases hnone with ⟨h01, h12, h23, h34, h40⟩

  have hx1 := x1.isLt
  have hx2 := x2.isLt
  have hx3 := x3.isLt
  have hx4 := x4.isLt

  have bounds2 : 4 ≤ x2.val ∧ x2.val ≤ 29 := by
    unfold circularDistance at h02
    omega
  have bounds3 : 4 ≤ x3.val ∧ x3.val ≤ 29 := by
    unfold circularDistance at h03
    omega
  have side1 : x1.val ≤ 3 ∨ 30 ≤ x1.val := by
    unfold circularDistance at h01
    omega
  have side4 : x4.val ≤ 3 ∨ 30 ≤ x4.val := by
    unfold circularDistance at h40
    omega

  rcases side1 with low1 | high1
  · rcases side4 with low4 | high4
    · unfold circularDistance at h14
      omega
    · have low2 : x2.val ≤ 6 := by
        unfold circularDistance at h12
        omega
      have high3 : 27 ≤ x3.val := by
        unfold circularDistance at h34
        omega
      unfold circularDistance at h23
      omega
  · rcases side4 with low4 | high4
    · have high2 : 27 ≤ x2.val := by
        unfold circularDistance at h12
        omega
      have low3 : x3.val ≤ 6 := by
        unfold circularDistance at h34
        omega
      unfold circularDistance at h23
      omega
    · unfold circularDistance at h14
      omega

end CircularColoring

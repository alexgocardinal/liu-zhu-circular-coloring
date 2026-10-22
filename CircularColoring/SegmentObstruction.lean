import CircularColoring.SlowFibers

namespace CircularColoring

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def IsSegmentColoring (f : Fin 5 → Fin 9) : Prop :=
  ∀ i j : Fin 5,
    2 ≤ circularDistance 5 i.val j.val →
    4 ≤ circularDistance 33 (f i).val (f j).val

def SegmentsCompatible
    (d : Nat)
    (f g : Fin 5 → Fin 9) : Prop :=
  ∀ i j : Fin 5,
    2 ≤ circularDistance 5 i.val j.val →
    4 ≤ circularDistance 33 (f i).val (d + (g j).val)

def segmentPatterns : Fin 150 → (Fin 5 → Fin 9) :=
  ![![0, 0, 4, 4, 8],
    ![0, 0, 4, 5, 8],
    ![0, 0, 4, 6, 8],
    ![0, 0, 4, 7, 8],
    ![0, 0, 4, 8, 8],
    ![0, 0, 8, 4, 4],
    ![0, 0, 8, 5, 4],
    ![0, 0, 8, 6, 4],
    ![0, 0, 8, 7, 4],
    ![0, 0, 8, 8, 4],
    ![0, 1, 4, 5, 8],
    ![0, 1, 4, 6, 8],
    ![0, 1, 4, 7, 8],
    ![0, 1, 4, 8, 8],
    ![0, 2, 4, 6, 8],
    ![0, 2, 4, 7, 8],
    ![0, 2, 4, 8, 8],
    ![0, 3, 4, 7, 8],
    ![0, 3, 4, 8, 8],
    ![0, 4, 4, 8, 0],
    ![0, 4, 4, 8, 8],
    ![0, 4, 5, 8, 0],
    ![0, 4, 6, 8, 0],
    ![0, 4, 7, 8, 0],
    ![0, 4, 8, 8, 0],
    ![0, 8, 4, 4, 0],
    ![0, 8, 5, 4, 0],
    ![0, 8, 5, 4, 1],
    ![0, 8, 6, 4, 0],
    ![0, 8, 6, 4, 1],
    ![0, 8, 6, 4, 2],
    ![0, 8, 7, 4, 0],
    ![0, 8, 7, 4, 1],
    ![0, 8, 7, 4, 2],
    ![0, 8, 7, 4, 3],
    ![0, 8, 8, 4, 0],
    ![0, 8, 8, 4, 1],
    ![0, 8, 8, 4, 2],
    ![0, 8, 8, 4, 3],
    ![0, 8, 8, 4, 4],
    ![1, 0, 8, 5, 4],
    ![1, 0, 8, 6, 4],
    ![1, 0, 8, 7, 4],
    ![1, 0, 8, 8, 4],
    ![1, 4, 5, 8, 0],
    ![1, 4, 6, 8, 0],
    ![1, 4, 7, 8, 0],
    ![1, 4, 8, 8, 0],
    ![2, 0, 8, 6, 4],
    ![2, 0, 8, 7, 4],
    ![2, 0, 8, 8, 4],
    ![2, 4, 6, 8, 0],
    ![2, 4, 7, 8, 0],
    ![2, 4, 8, 8, 0],
    ![3, 0, 8, 7, 4],
    ![3, 0, 8, 8, 4],
    ![3, 4, 7, 8, 0],
    ![3, 4, 8, 8, 0],
    ![4, 0, 0, 8, 4],
    ![4, 0, 0, 8, 5],
    ![4, 0, 0, 8, 6],
    ![4, 0, 0, 8, 7],
    ![4, 0, 0, 8, 8],
    ![4, 0, 8, 8, 4],
    ![4, 1, 0, 8, 5],
    ![4, 1, 0, 8, 6],
    ![4, 1, 0, 8, 7],
    ![4, 1, 0, 8, 8],
    ![4, 2, 0, 8, 6],
    ![4, 2, 0, 8, 7],
    ![4, 2, 0, 8, 8],
    ![4, 3, 0, 8, 7],
    ![4, 3, 0, 8, 8],
    ![4, 4, 0, 0, 8],
    ![4, 4, 0, 8, 8],
    ![4, 4, 8, 0, 0],
    ![4, 4, 8, 8, 0],
    ![4, 5, 8, 0, 0],
    ![4, 5, 8, 0, 1],
    ![4, 6, 8, 0, 0],
    ![4, 6, 8, 0, 1],
    ![4, 6, 8, 0, 2],
    ![4, 7, 8, 0, 0],
    ![4, 7, 8, 0, 1],
    ![4, 7, 8, 0, 2],
    ![4, 7, 8, 0, 3],
    ![4, 8, 0, 0, 4],
    ![4, 8, 8, 0, 0],
    ![4, 8, 8, 0, 1],
    ![4, 8, 8, 0, 2],
    ![4, 8, 8, 0, 3],
    ![4, 8, 8, 0, 4],
    ![5, 4, 0, 0, 8],
    ![5, 4, 1, 0, 8],
    ![5, 8, 0, 0, 4],
    ![5, 8, 0, 1, 4],
    ![6, 4, 0, 0, 8],
    ![6, 4, 1, 0, 8],
    ![6, 4, 2, 0, 8],
    ![6, 8, 0, 0, 4],
    ![6, 8, 0, 1, 4],
    ![6, 8, 0, 2, 4],
    ![7, 4, 0, 0, 8],
    ![7, 4, 1, 0, 8],
    ![7, 4, 2, 0, 8],
    ![7, 4, 3, 0, 8],
    ![7, 8, 0, 0, 4],
    ![7, 8, 0, 1, 4],
    ![7, 8, 0, 2, 4],
    ![7, 8, 0, 3, 4],
    ![8, 0, 0, 4, 4],
    ![8, 0, 0, 4, 5],
    ![8, 0, 0, 4, 6],
    ![8, 0, 0, 4, 7],
    ![8, 0, 0, 4, 8],
    ![8, 0, 1, 4, 5],
    ![8, 0, 1, 4, 6],
    ![8, 0, 1, 4, 7],
    ![8, 0, 1, 4, 8],
    ![8, 0, 2, 4, 6],
    ![8, 0, 2, 4, 7],
    ![8, 0, 2, 4, 8],
    ![8, 0, 3, 4, 7],
    ![8, 0, 3, 4, 8],
    ![8, 0, 4, 4, 8],
    ![8, 4, 0, 0, 8],
    ![8, 4, 1, 0, 8],
    ![8, 4, 2, 0, 8],
    ![8, 4, 3, 0, 8],
    ![8, 4, 4, 0, 0],
    ![8, 4, 4, 0, 8],
    ![8, 5, 4, 0, 0],
    ![8, 5, 4, 1, 0],
    ![8, 6, 4, 0, 0],
    ![8, 6, 4, 1, 0],
    ![8, 6, 4, 2, 0],
    ![8, 7, 4, 0, 0],
    ![8, 7, 4, 1, 0],
    ![8, 7, 4, 2, 0],
    ![8, 7, 4, 3, 0],
    ![8, 8, 0, 0, 4],
    ![8, 8, 0, 1, 4],
    ![8, 8, 0, 2, 4],
    ![8, 8, 0, 3, 4],
    ![8, 8, 0, 4, 4],
    ![8, 8, 4, 0, 0],
    ![8, 8, 4, 1, 0],
    ![8, 8, 4, 2, 0],
    ![8, 8, 4, 3, 0],
    ![8, 8, 4, 4, 0]]

run_cmd Lean.logInfo "Starting 81 small completeness checks."

theorem segmentComplete_0_0 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![0, 0, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![0, 0, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_0_1 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![0, 1, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![0, 1, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_0_2 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![0, 2, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![0, 2, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_0_3 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![0, 3, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![0, 3, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_0_4 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![0, 4, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![0, 4, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_0_5 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![0, 5, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![0, 5, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_0_6 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![0, 6, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![0, 6, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_0_7 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![0, 7, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![0, 7, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_0_8 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![0, 8, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![0, 8, c, d, e] := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness: 9/81 checks passed."

theorem segmentComplete_1_0 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![1, 0, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![1, 0, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_1_1 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![1, 1, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![1, 1, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_1_2 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![1, 2, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![1, 2, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_1_3 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![1, 3, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![1, 3, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_1_4 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![1, 4, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![1, 4, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_1_5 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![1, 5, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![1, 5, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_1_6 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![1, 6, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![1, 6, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_1_7 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![1, 7, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![1, 7, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_1_8 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![1, 8, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![1, 8, c, d, e] := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness: 18/81 checks passed."

theorem segmentComplete_2_0 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![2, 0, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![2, 0, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_2_1 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![2, 1, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![2, 1, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_2_2 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![2, 2, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![2, 2, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_2_3 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![2, 3, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![2, 3, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_2_4 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![2, 4, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![2, 4, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_2_5 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![2, 5, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![2, 5, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_2_6 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![2, 6, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![2, 6, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_2_7 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![2, 7, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![2, 7, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_2_8 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![2, 8, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![2, 8, c, d, e] := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness: 27/81 checks passed."

theorem segmentComplete_3_0 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![3, 0, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![3, 0, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_3_1 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![3, 1, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![3, 1, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_3_2 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![3, 2, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![3, 2, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_3_3 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![3, 3, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![3, 3, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_3_4 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![3, 4, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![3, 4, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_3_5 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![3, 5, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![3, 5, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_3_6 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![3, 6, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![3, 6, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_3_7 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![3, 7, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![3, 7, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_3_8 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![3, 8, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![3, 8, c, d, e] := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness: 36/81 checks passed."

theorem segmentComplete_4_0 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![4, 0, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![4, 0, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_4_1 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![4, 1, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![4, 1, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_4_2 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![4, 2, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![4, 2, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_4_3 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![4, 3, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![4, 3, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_4_4 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![4, 4, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![4, 4, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_4_5 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![4, 5, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![4, 5, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_4_6 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![4, 6, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![4, 6, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_4_7 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![4, 7, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![4, 7, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_4_8 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![4, 8, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![4, 8, c, d, e] := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness: 45/81 checks passed."

theorem segmentComplete_5_0 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![5, 0, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![5, 0, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_5_1 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![5, 1, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![5, 1, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_5_2 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![5, 2, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![5, 2, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_5_3 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![5, 3, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![5, 3, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_5_4 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![5, 4, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![5, 4, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_5_5 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![5, 5, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![5, 5, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_5_6 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![5, 6, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![5, 6, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_5_7 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![5, 7, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![5, 7, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_5_8 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![5, 8, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![5, 8, c, d, e] := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness: 54/81 checks passed."

theorem segmentComplete_6_0 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![6, 0, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![6, 0, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_6_1 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![6, 1, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![6, 1, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_6_2 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![6, 2, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![6, 2, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_6_3 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![6, 3, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![6, 3, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_6_4 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![6, 4, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![6, 4, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_6_5 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![6, 5, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![6, 5, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_6_6 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![6, 6, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![6, 6, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_6_7 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![6, 7, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![6, 7, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_6_8 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![6, 8, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![6, 8, c, d, e] := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness: 63/81 checks passed."

theorem segmentComplete_7_0 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![7, 0, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![7, 0, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_7_1 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![7, 1, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![7, 1, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_7_2 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![7, 2, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![7, 2, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_7_3 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![7, 3, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![7, 3, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_7_4 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![7, 4, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![7, 4, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_7_5 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![7, 5, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![7, 5, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_7_6 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![7, 6, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![7, 6, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_7_7 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![7, 7, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![7, 7, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_7_8 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![7, 8, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![7, 8, c, d, e] := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness: 72/81 checks passed."

theorem segmentComplete_8_0 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![8, 0, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![8, 0, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_8_1 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![8, 1, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![8, 1, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_8_2 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![8, 2, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![8, 2, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_8_3 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![8, 3, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![8, 3, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_8_4 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![8, 4, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![8, 4, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_8_5 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![8, 5, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![8, 5, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_8_6 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![8, 6, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![8, 6, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_8_7 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![8, 7, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![8, 7, c, d, e] := by
  unfold IsSegmentColoring
  decide

theorem segmentComplete_8_8 :
    ∀ c d e : Fin 9,
      IsSegmentColoring
        (![8, 8, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150,
        segmentPatterns k = ![8, 8, c, d, e] := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness: 81/81 checks passed."

theorem segmentPatterns_complete_values :
    ∀ a b c d e : Fin 9,
      IsSegmentColoring (![a, b, c, d, e] : Fin 5 → Fin 9) →
      ∃ k : Fin 150, segmentPatterns k = ![a, b, c, d, e] := by
  intro a b c d e h
  fin_cases a <;> fin_cases b
  · exact segmentComplete_0_0 c d e h
  · exact segmentComplete_0_1 c d e h
  · exact segmentComplete_0_2 c d e h
  · exact segmentComplete_0_3 c d e h
  · exact segmentComplete_0_4 c d e h
  · exact segmentComplete_0_5 c d e h
  · exact segmentComplete_0_6 c d e h
  · exact segmentComplete_0_7 c d e h
  · exact segmentComplete_0_8 c d e h
  · exact segmentComplete_1_0 c d e h
  · exact segmentComplete_1_1 c d e h
  · exact segmentComplete_1_2 c d e h
  · exact segmentComplete_1_3 c d e h
  · exact segmentComplete_1_4 c d e h
  · exact segmentComplete_1_5 c d e h
  · exact segmentComplete_1_6 c d e h
  · exact segmentComplete_1_7 c d e h
  · exact segmentComplete_1_8 c d e h
  · exact segmentComplete_2_0 c d e h
  · exact segmentComplete_2_1 c d e h
  · exact segmentComplete_2_2 c d e h
  · exact segmentComplete_2_3 c d e h
  · exact segmentComplete_2_4 c d e h
  · exact segmentComplete_2_5 c d e h
  · exact segmentComplete_2_6 c d e h
  · exact segmentComplete_2_7 c d e h
  · exact segmentComplete_2_8 c d e h
  · exact segmentComplete_3_0 c d e h
  · exact segmentComplete_3_1 c d e h
  · exact segmentComplete_3_2 c d e h
  · exact segmentComplete_3_3 c d e h
  · exact segmentComplete_3_4 c d e h
  · exact segmentComplete_3_5 c d e h
  · exact segmentComplete_3_6 c d e h
  · exact segmentComplete_3_7 c d e h
  · exact segmentComplete_3_8 c d e h
  · exact segmentComplete_4_0 c d e h
  · exact segmentComplete_4_1 c d e h
  · exact segmentComplete_4_2 c d e h
  · exact segmentComplete_4_3 c d e h
  · exact segmentComplete_4_4 c d e h
  · exact segmentComplete_4_5 c d e h
  · exact segmentComplete_4_6 c d e h
  · exact segmentComplete_4_7 c d e h
  · exact segmentComplete_4_8 c d e h
  · exact segmentComplete_5_0 c d e h
  · exact segmentComplete_5_1 c d e h
  · exact segmentComplete_5_2 c d e h
  · exact segmentComplete_5_3 c d e h
  · exact segmentComplete_5_4 c d e h
  · exact segmentComplete_5_5 c d e h
  · exact segmentComplete_5_6 c d e h
  · exact segmentComplete_5_7 c d e h
  · exact segmentComplete_5_8 c d e h
  · exact segmentComplete_6_0 c d e h
  · exact segmentComplete_6_1 c d e h
  · exact segmentComplete_6_2 c d e h
  · exact segmentComplete_6_3 c d e h
  · exact segmentComplete_6_4 c d e h
  · exact segmentComplete_6_5 c d e h
  · exact segmentComplete_6_6 c d e h
  · exact segmentComplete_6_7 c d e h
  · exact segmentComplete_6_8 c d e h
  · exact segmentComplete_7_0 c d e h
  · exact segmentComplete_7_1 c d e h
  · exact segmentComplete_7_2 c d e h
  · exact segmentComplete_7_3 c d e h
  · exact segmentComplete_7_4 c d e h
  · exact segmentComplete_7_5 c d e h
  · exact segmentComplete_7_6 c d e h
  · exact segmentComplete_7_7 c d e h
  · exact segmentComplete_7_8 c d e h
  · exact segmentComplete_8_0 c d e h
  · exact segmentComplete_8_1 c d e h
  · exact segmentComplete_8_2 c d e h
  · exact segmentComplete_8_3 c d e h
  · exact segmentComplete_8_4 c d e h
  · exact segmentComplete_8_5 c d e h
  · exact segmentComplete_8_6 c d e h
  · exact segmentComplete_8_7 c d e h
  · exact segmentComplete_8_8 c d e h

theorem segmentPatterns_complete :
    ∀ f : Fin 5 → Fin 9,
      IsSegmentColoring f →
      ∃ k : Fin 150, segmentPatterns k = f := by
  intro f hf
  have hfun :
      (![f 0, f 1, f 2, f 3, f 4] : Fin 5 → Fin 9) = f := by
    funext i
    fin_cases i <;> rfl
  have hf' :
      IsSegmentColoring
        (![f 0, f 1, f 2, f 3, f 4] : Fin 5 → Fin 9) := by
    rw [hfun]
    exact hf
  obtain ⟨k, hk⟩ := segmentPatterns_complete_values
    (f 0) (f 1) (f 2) (f 3) (f 4) hf'
  rw [hfun] at hk
  exact ⟨k, hk⟩


theorem segmentPatterns_valid :
    ∀ k : Fin 150, IsSegmentColoring (segmentPatterns k) := by
  unfold IsSegmentColoring
  decide

run_cmd Lean.logInfo "Completeness finished. Starting compatibility checks."

theorem segmentNoTriple_0 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 0) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 0) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_1 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 1) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 1) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_2 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 2) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 2) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_3 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 3) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 3) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_4 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 4) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 4) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_5 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 5) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 5) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_6 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 6) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 6) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_7 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 7) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 7) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_8 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 8) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 8) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_9 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 9) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 9) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_10 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 10) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 10) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_11 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 11) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 11) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_12 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 12) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 12) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_13 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 13) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 13) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_14 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 14) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 14) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_15 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 15) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 15) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_16 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 16) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 16) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_17 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 17) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 17) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_18 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 18) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 18) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_19 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 19) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 19) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_20 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 20) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 20) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_21 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 21) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 21) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_22 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 22) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 22) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_23 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 23) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 23) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_24 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 24) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 24) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

run_cmd Lean.logInfo "Compatibility: 25/150 checks passed."

theorem segmentNoTriple_25 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 25) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 25) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_26 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 26) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 26) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_27 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 27) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 27) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_28 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 28) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 28) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_29 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 29) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 29) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_30 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 30) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 30) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_31 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 31) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 31) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_32 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 32) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 32) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_33 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 33) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 33) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_34 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 34) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 34) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_35 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 35) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 35) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_36 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 36) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 36) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_37 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 37) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 37) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_38 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 38) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 38) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_39 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 39) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 39) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_40 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 40) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 40) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_41 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 41) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 41) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_42 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 42) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 42) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_43 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 43) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 43) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_44 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 44) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 44) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_45 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 45) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 45) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_46 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 46) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 46) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_47 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 47) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 47) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_48 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 48) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 48) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_49 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 49) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 49) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

run_cmd Lean.logInfo "Compatibility: 50/150 checks passed."

theorem segmentNoTriple_50 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 50) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 50) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_51 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 51) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 51) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_52 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 52) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 52) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_53 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 53) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 53) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_54 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 54) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 54) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_55 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 55) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 55) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_56 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 56) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 56) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_57 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 57) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 57) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_58 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 58) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 58) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_59 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 59) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 59) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_60 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 60) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 60) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_61 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 61) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 61) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_62 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 62) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 62) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_63 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 63) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 63) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_64 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 64) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 64) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_65 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 65) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 65) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_66 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 66) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 66) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_67 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 67) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 67) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_68 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 68) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 68) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_69 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 69) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 69) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_70 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 70) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 70) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_71 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 71) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 71) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_72 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 72) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 72) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_73 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 73) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 73) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_74 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 74) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 74) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

run_cmd Lean.logInfo "Compatibility: 75/150 checks passed."

theorem segmentNoTriple_75 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 75) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 75) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_76 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 76) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 76) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_77 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 77) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 77) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_78 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 78) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 78) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_79 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 79) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 79) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_80 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 80) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 80) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_81 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 81) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 81) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_82 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 82) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 82) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_83 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 83) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 83) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_84 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 84) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 84) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_85 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 85) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 85) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_86 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 86) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 86) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_87 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 87) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 87) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_88 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 88) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 88) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_89 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 89) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 89) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_90 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 90) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 90) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_91 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 91) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 91) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_92 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 92) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 92) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_93 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 93) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 93) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_94 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 94) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 94) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_95 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 95) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 95) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_96 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 96) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 96) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_97 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 97) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 97) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_98 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 98) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 98) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_99 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 99) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 99) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

run_cmd Lean.logInfo "Compatibility: 100/150 checks passed."

theorem segmentNoTriple_100 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 100) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 100) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_101 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 101) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 101) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_102 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 102) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 102) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_103 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 103) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 103) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_104 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 104) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 104) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_105 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 105) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 105) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_106 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 106) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 106) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_107 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 107) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 107) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_108 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 108) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 108) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_109 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 109) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 109) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_110 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 110) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 110) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_111 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 111) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 111) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_112 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 112) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 112) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_113 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 113) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 113) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_114 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 114) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 114) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_115 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 115) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 115) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_116 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 116) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 116) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_117 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 117) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 117) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_118 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 118) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 118) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_119 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 119) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 119) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_120 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 120) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 120) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_121 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 121) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 121) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_122 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 122) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 122) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_123 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 123) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 123) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_124 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 124) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 124) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

run_cmd Lean.logInfo "Compatibility: 125/150 checks passed."

theorem segmentNoTriple_125 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 125) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 125) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_126 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 126) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 126) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_127 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 127) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 127) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_128 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 128) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 128) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_129 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 129) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 129) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_130 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 130) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 130) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_131 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 131) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 131) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_132 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 132) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 132) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_133 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 133) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 133) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_134 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 134) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 134) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_135 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 135) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 135) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_136 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 136) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 136) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_137 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 137) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 137) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_138 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 138) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 138) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_139 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 139) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 139) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_140 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 140) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 140) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_141 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 141) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 141) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_142 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 142) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 142) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_143 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 143) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 143) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_144 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 144) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 144) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_145 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 145) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 145) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_146 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 146) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 146) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_147 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 147) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 147) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_148 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 148) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 148) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

theorem segmentNoTriple_149 :
    ∀ j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns 149) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns 149) (segmentPatterns k) := by
  unfold SegmentsCompatible
  decide

run_cmd Lean.logInfo "Compatibility: 150/150 checks passed."

theorem segmentPatterns_no_triple :
    ∀ i j : Fin 150,
      SegmentsCompatible 3 (segmentPatterns i) (segmentPatterns j) →
      ∀ k : Fin 150,
        SegmentsCompatible 3 (segmentPatterns j) (segmentPatterns k) →
        ¬ SegmentsCompatible 6 (segmentPatterns i) (segmentPatterns k) := by
  intro i
  fin_cases i
  · exact segmentNoTriple_0
  · exact segmentNoTriple_1
  · exact segmentNoTriple_2
  · exact segmentNoTriple_3
  · exact segmentNoTriple_4
  · exact segmentNoTriple_5
  · exact segmentNoTriple_6
  · exact segmentNoTriple_7
  · exact segmentNoTriple_8
  · exact segmentNoTriple_9
  · exact segmentNoTriple_10
  · exact segmentNoTriple_11
  · exact segmentNoTriple_12
  · exact segmentNoTriple_13
  · exact segmentNoTriple_14
  · exact segmentNoTriple_15
  · exact segmentNoTriple_16
  · exact segmentNoTriple_17
  · exact segmentNoTriple_18
  · exact segmentNoTriple_19
  · exact segmentNoTriple_20
  · exact segmentNoTriple_21
  · exact segmentNoTriple_22
  · exact segmentNoTriple_23
  · exact segmentNoTriple_24
  · exact segmentNoTriple_25
  · exact segmentNoTriple_26
  · exact segmentNoTriple_27
  · exact segmentNoTriple_28
  · exact segmentNoTriple_29
  · exact segmentNoTriple_30
  · exact segmentNoTriple_31
  · exact segmentNoTriple_32
  · exact segmentNoTriple_33
  · exact segmentNoTriple_34
  · exact segmentNoTriple_35
  · exact segmentNoTriple_36
  · exact segmentNoTriple_37
  · exact segmentNoTriple_38
  · exact segmentNoTriple_39
  · exact segmentNoTriple_40
  · exact segmentNoTriple_41
  · exact segmentNoTriple_42
  · exact segmentNoTriple_43
  · exact segmentNoTriple_44
  · exact segmentNoTriple_45
  · exact segmentNoTriple_46
  · exact segmentNoTriple_47
  · exact segmentNoTriple_48
  · exact segmentNoTriple_49
  · exact segmentNoTriple_50
  · exact segmentNoTriple_51
  · exact segmentNoTriple_52
  · exact segmentNoTriple_53
  · exact segmentNoTriple_54
  · exact segmentNoTriple_55
  · exact segmentNoTriple_56
  · exact segmentNoTriple_57
  · exact segmentNoTriple_58
  · exact segmentNoTriple_59
  · exact segmentNoTriple_60
  · exact segmentNoTriple_61
  · exact segmentNoTriple_62
  · exact segmentNoTriple_63
  · exact segmentNoTriple_64
  · exact segmentNoTriple_65
  · exact segmentNoTriple_66
  · exact segmentNoTriple_67
  · exact segmentNoTriple_68
  · exact segmentNoTriple_69
  · exact segmentNoTriple_70
  · exact segmentNoTriple_71
  · exact segmentNoTriple_72
  · exact segmentNoTriple_73
  · exact segmentNoTriple_74
  · exact segmentNoTriple_75
  · exact segmentNoTriple_76
  · exact segmentNoTriple_77
  · exact segmentNoTriple_78
  · exact segmentNoTriple_79
  · exact segmentNoTriple_80
  · exact segmentNoTriple_81
  · exact segmentNoTriple_82
  · exact segmentNoTriple_83
  · exact segmentNoTriple_84
  · exact segmentNoTriple_85
  · exact segmentNoTriple_86
  · exact segmentNoTriple_87
  · exact segmentNoTriple_88
  · exact segmentNoTriple_89
  · exact segmentNoTriple_90
  · exact segmentNoTriple_91
  · exact segmentNoTriple_92
  · exact segmentNoTriple_93
  · exact segmentNoTriple_94
  · exact segmentNoTriple_95
  · exact segmentNoTriple_96
  · exact segmentNoTriple_97
  · exact segmentNoTriple_98
  · exact segmentNoTriple_99
  · exact segmentNoTriple_100
  · exact segmentNoTriple_101
  · exact segmentNoTriple_102
  · exact segmentNoTriple_103
  · exact segmentNoTriple_104
  · exact segmentNoTriple_105
  · exact segmentNoTriple_106
  · exact segmentNoTriple_107
  · exact segmentNoTriple_108
  · exact segmentNoTriple_109
  · exact segmentNoTriple_110
  · exact segmentNoTriple_111
  · exact segmentNoTriple_112
  · exact segmentNoTriple_113
  · exact segmentNoTriple_114
  · exact segmentNoTriple_115
  · exact segmentNoTriple_116
  · exact segmentNoTriple_117
  · exact segmentNoTriple_118
  · exact segmentNoTriple_119
  · exact segmentNoTriple_120
  · exact segmentNoTriple_121
  · exact segmentNoTriple_122
  · exact segmentNoTriple_123
  · exact segmentNoTriple_124
  · exact segmentNoTriple_125
  · exact segmentNoTriple_126
  · exact segmentNoTriple_127
  · exact segmentNoTriple_128
  · exact segmentNoTriple_129
  · exact segmentNoTriple_130
  · exact segmentNoTriple_131
  · exact segmentNoTriple_132
  · exact segmentNoTriple_133
  · exact segmentNoTriple_134
  · exact segmentNoTriple_135
  · exact segmentNoTriple_136
  · exact segmentNoTriple_137
  · exact segmentNoTriple_138
  · exact segmentNoTriple_139
  · exact segmentNoTriple_140
  · exact segmentNoTriple_141
  · exact segmentNoTriple_142
  · exact segmentNoTriple_143
  · exact segmentNoTriple_144
  · exact segmentNoTriple_145
  · exact segmentNoTriple_146
  · exact segmentNoTriple_147
  · exact segmentNoTriple_148
  · exact segmentNoTriple_149

theorem no_three_segment_colorings
    (f g h : Fin 5 → Fin 9)
    (hf : IsSegmentColoring f)
    (hg : IsSegmentColoring g)
    (hh : IsSegmentColoring h)
    (hfg : SegmentsCompatible 3 f g)
    (hgh : SegmentsCompatible 3 g h)
    (hfh : SegmentsCompatible 6 f h) :
    False := by
  obtain ⟨i, hi⟩ := segmentPatterns_complete f hf
  obtain ⟨j, hj⟩ := segmentPatterns_complete g hg
  obtain ⟨k, hk⟩ := segmentPatterns_complete h hh
  rw [← hi, ← hj] at hfg
  rw [← hj, ← hk] at hgh
  rw [← hi, ← hk] at hfh
  exact segmentPatterns_no_triple i j hfg k hgh hfh

end CircularColoring

run_cmd Lean.logInfo "All segment obstruction checks finished."

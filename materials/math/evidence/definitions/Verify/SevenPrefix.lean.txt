import Verify.AtomicSemantics

/-! An all-n no-flip upper-bound construction in the existing full typed
atomic semantics. No minimality or Python runtime claim. -/

namespace Verify.SevenPrefixUpperBound

open AtomicSemantics ResearchWords ROperationConnection

def prefixMoves : List AtomicSemantics.Move := [.m9, .m3, .m6, .m2, .m2, .m5, .m11]

def stage1 (n : ℕ) : GroupState :=
  (Y * X * y ^ n * x * Y ^ n, vFamily n)
def stage2 (n : ℕ) : GroupState := (Y * X * y ^ n, vFamily n)
def stage3 (n : ℕ) : GroupState := (x * Y * X * y ^ n * X, vFamily n)
def stage4 (n : ℕ) : GroupState := (x * Y * X, vFamily n)
def stage5 (n : ℕ) : GroupState := (x * Y ^ (n + 1), vFamily n)
def stage6 (n : ℕ) : GroupState := (x * Y ^ (n + 1), x * y * X)

theorem step1 (n : ℕ) :
    groupStep .m9 (initial n) = stage1 n := by
  apply Prod.ext <;>
    simp [groupStep, initial, uFamily, vFamily, stage1, X, Y,
      pow_succ, mul_assoc]

theorem step2 (n : ℕ) : groupStep .m3 (stage1 n) = stage2 n := by
  apply Prod.ext <;> simp [groupStep, stage1, stage2, vFamily, X, Y, mul_assoc]

theorem step3 (n : ℕ) : groupStep .m6 (stage2 n) = stage3 n := by
  apply Prod.ext <;> simp [groupStep, stage2, stage3, mul_assoc]

theorem step4 (n : ℕ) : groupStep .m2 (stage3 n) = stage4 n := by
  apply Prod.ext <;> simp [groupStep, stage3, stage4, vFamily, X, Y, mul_assoc]

theorem step5 (n : ℕ) : groupStep .m2 (stage4 n) = stage5 n := by
  apply Prod.ext <;>
    simp [groupStep, stage4, stage5, vFamily, X, Y, pow_succ', mul_assoc]

theorem step6 (n : ℕ) : groupStep .m5 (stage5 n) = stage6 n := by
  apply Prod.ext <;>
    simp [groupStep, stage5, stage6, vFamily, X, Y, pow_succ', mul_assoc]

theorem step7 (n : ℕ) : groupStep .m11 (stage6 n) = (x * Y ^ (n + 1), y) := by
  apply Prod.ext <;> simp [groupStep, stage6, X, mul_assoc]

theorem prefix_run (n : ℕ) :
    groupRun prefixMoves (initial n) = (x * Y ^ (n + 1), y) := by
  simp only [prefixMoves, groupRun, step1, step2, step3, step4, step5, step6, step7]

theorem prefix_run_zpow (n : ℕ) :
    groupRun prefixMoves (initial n) = (x * y ^ (-((n + 1 : ℕ) : ℤ)), y) := by
  rw [prefix_run, zpow_neg, zpow_natCast]
  simp only [Y, inv_pow]

theorem groupRun_append (a b : List AtomicSemantics.Move) (s : GroupState) :
    groupRun (a ++ b) s = groupRun b (groupRun a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons m a ih => simpa only [List.cons_append, groupRun] using ih (groupStep m s)

theorem run_twos (k : ℕ) (r s : F) :
    groupRun (List.replicate k .m2) (r, s) = (r * s ^ k, s) := by
  induction k generalizing r with
  | zero => simp [groupRun]
  | succ k ih =>
      simp [List.replicate_succ, groupRun, groupStep, ih, pow_succ', mul_assoc]

def word (n : ℕ) : List AtomicSemantics.Move :=
  prefixMoves ++ List.replicate (n + 1) .m2

theorem reaches (n : ℕ) : groupRun (word n) (initial n) = (x, y) := by
  rw [word, groupRun_append, prefix_run, run_twos]
  simp [Y, mul_assoc]

theorem word_length (n : ℕ) : (word n).length = n + 8 := by
  simp [word, prefixMoves]

theorem prefix_valid (m : AtomicSemantics.Move) (hm : m ∈ prefixMoves) :
    2 ≤ AtomicSemantics.moveId m ∧ AtomicSemantics.moveId m ≤ 13 := by
  simp [prefixMoves] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem word_valid (n : ℕ) (m : AtomicSemantics.Move) (hm : m ∈ word n) :
    2 ≤ AtomicSemantics.moveId m ∧ AtomicSemantics.moveId m ≤ 13 := by
  change m ∈ prefixMoves ++ List.replicate (n + 1) .m2 at hm
  rcases List.mem_append.mp hm with hp | ht
  · exact prefix_valid m hp
  · rcases List.mem_replicate.mp ht with ⟨_, rfl⟩
    decide

theorem word_no_flips (n : ℕ) (m : AtomicSemantics.Move) (hm : m ∈ word n) :
    m ≠ .m0 ∧ m ≠ .m1 := by
  have hv := word_valid n m hm
  constructor <;> intro he <;> subst m <;> norm_num [AtomicSemantics.moveId] at hv

theorem prefix_zero : groupRun prefixMoves (initial 0) = (x * Y, y) := by
  simpa using prefix_run 0

theorem reaches_zero : groupRun (word 0) (initial 0) = (x, y) := reaches 0

theorem zero_ids : (word 0).map AtomicSemantics.moveId = [9,3,6,2,2,5,11,2] := by
  decide +kernel

theorem six_ids : (word 6).map AtomicSemantics.moveId =
    [9,3,6,2,2,5,11,2,2,2,2,2,2,2] := by
  decide +kernel

/-- The boundary input is the group pair (Y,x), even though the initial
literal X*x*Y display contains a cancellation at n=0. -/
theorem initial_zero : initial 0 = (Y, x) := by
  simp [initial, uFamily, vFamily, X, Y]

theorem zero_raw_initial_not_reduced : ¬ ReducedState (initialWords 0) := by
  dsimp [ReducedState, initialWords, FreeGroup.IsReduced]
  decide +kernel

/-- Canonical initial words remove the raw n=0 cancellation before replay. -/
def canonicalInitial (n : ℕ) : WordState :=
  ((uFamily n).toWord, (vFamily n).toWord)

theorem canonicalInitial_reduced (n : ℕ) : ReducedState (canonicalInitial n) :=
  ⟨FreeGroup.isReduced_toWord, FreeGroup.isReduced_toWord⟩

theorem eval_canonicalInitial (n : ℕ) : evalState (canonicalInitial n) = initial n := by
  simp only [canonicalInitial, evalState, initial, FreeGroup.mk_toWord]

theorem canonical_reaches (n : ℕ) :
    wordRun (word n) (canonicalInitial n) =
      ([ReducedWords.xLetter], [ReducedWords.yLetter]) := by
  rw [wordRun_canonical _ _ (canonicalInitial_reduced n), eval_canonicalInitial, reaches]
  rfl

theorem canonical_zero : canonicalInitial 0 =
    ([ReducedWords.YLetter], [ReducedWords.xLetter]) := by
  decide +kernel

theorem suffix_stage (n k : ℕ) (hk : k ≤ n + 1) :
    groupRun (List.replicate k .m2) (x * Y ^ (n + 1), y) =
      (x * Y ^ (n + 1 - k), y) := by
  have hp : Y ^ (n + 1) = Y ^ (n + 1 - k) * Y ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [run_twos, hp]
  simp [Y, mul_assoc]

open ReducedWords

theorem zero_trace :
    (List.range 8).map (fun k =>
      wordRun (prefixMoves.take k) ([YLetter], [xLetter])) =
      [([YLetter], [xLetter]), ([YLetter], [xLetter]),
       ([YLetter, XLetter], [xLetter]),
       ([xLetter, YLetter, XLetter, XLetter], [xLetter]),
       ([xLetter, YLetter, XLetter], [xLetter]),
       ([xLetter, YLetter], [xLetter]),
       ([xLetter, YLetter], [xLetter, yLetter, XLetter]),
       ([xLetter, YLetter], [yLetter])] := by
  decide +kernel

end Verify.SevenPrefixUpperBound

#print axioms Verify.SevenPrefixUpperBound.step1
#print axioms Verify.SevenPrefixUpperBound.step2
#print axioms Verify.SevenPrefixUpperBound.step3
#print axioms Verify.SevenPrefixUpperBound.step4
#print axioms Verify.SevenPrefixUpperBound.step5
#print axioms Verify.SevenPrefixUpperBound.step6
#print axioms Verify.SevenPrefixUpperBound.step7
#print axioms Verify.SevenPrefixUpperBound.prefix_run
#print axioms Verify.SevenPrefixUpperBound.prefix_run_zpow
#print axioms Verify.SevenPrefixUpperBound.groupRun_append
#print axioms Verify.SevenPrefixUpperBound.run_twos
#print axioms Verify.SevenPrefixUpperBound.reaches
#print axioms Verify.SevenPrefixUpperBound.word_length
#print axioms Verify.SevenPrefixUpperBound.prefix_valid
#print axioms Verify.SevenPrefixUpperBound.word_valid
#print axioms Verify.SevenPrefixUpperBound.word_no_flips
#print axioms Verify.SevenPrefixUpperBound.prefix_zero
#print axioms Verify.SevenPrefixUpperBound.reaches_zero
#print axioms Verify.SevenPrefixUpperBound.zero_ids
#print axioms Verify.SevenPrefixUpperBound.six_ids

#print axioms Verify.SevenPrefixUpperBound.initial_zero
#print axioms Verify.SevenPrefixUpperBound.zero_raw_initial_not_reduced

#print axioms Verify.SevenPrefixUpperBound.canonicalInitial_reduced
#print axioms Verify.SevenPrefixUpperBound.eval_canonicalInitial
#print axioms Verify.SevenPrefixUpperBound.canonical_reaches
#print axioms Verify.SevenPrefixUpperBound.canonical_zero
#print axioms Verify.SevenPrefixUpperBound.suffix_stage
#print axioms Verify.SevenPrefixUpperBound.zero_trace

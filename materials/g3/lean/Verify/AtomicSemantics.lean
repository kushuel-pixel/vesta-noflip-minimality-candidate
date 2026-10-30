import Verify.ROperationConnection

/-! Full valid-ID word/group semantics inside Lean. Word normalization uses
Mathlib.reduce, not the Python stack implementation. No Python execution or
cross-language implementation equivalence is asserted. -/

namespace Verify.AtomicSemantics

abbrev Letter := ReducedWords.Letter
abbrev Word := List Letter
abbrev WordState := Word × Word
abbrev GroupState := ROperationConnection.State

inductive Move where
  | m0 | m1 | m2 | m3 | m4 | m5 | m6
  | m7 | m8 | m9 | m10 | m11 | m12 | m13
  deriving DecidableEq

def moveId : Move → ℕ
  | .m0 => 0 | .m1 => 1 | .m2 => 2 | .m3 => 3 | .m4 => 4 | .m5 => 5
  | .m6 => 6 | .m7 => 7 | .m8 => 8 | .m9 => 9 | .m10 => 10
  | .m11 => 11 | .m12 => 12 | .m13 => 13

def encodeLetter (a : Letter) : ℤ :=
  if a.2 then (a.1.val : ℤ) + 1 else -((a.1.val : ℤ) + 1)

def encodeWord (w : Word) : List ℤ := w.map encodeLetter

def evalState (w : WordState) : GroupState :=
  (FreeGroup.mk w.1, FreeGroup.mk w.2)

def wordConj (a : Letter) (w : Word) : Word :=
  FreeGroup.reduce ([a] ++ w ++ FreeGroup.invRev [a])

def wordStep : Move → WordState → WordState
  | .m0, (r, s) => (FreeGroup.invRev r, s)
  | .m1, (r, s) => (r, FreeGroup.invRev s)
  | .m2, (r, s) => (FreeGroup.reduce (r ++ s), s)
  | .m3, (r, s) => (FreeGroup.reduce (r ++ FreeGroup.invRev s), s)
  | .m4, (r, s) => (r, FreeGroup.reduce (s ++ r))
  | .m5, (r, s) => (r, FreeGroup.reduce (s ++ FreeGroup.invRev r))
  | .m6, (r, s) => (wordConj ReducedWords.xLetter r, s)
  | .m7, (r, s) => (wordConj ReducedWords.XLetter r, s)
  | .m8, (r, s) => (wordConj ReducedWords.yLetter r, s)
  | .m9, (r, s) => (wordConj ReducedWords.YLetter r, s)
  | .m10, (r, s) => (r, wordConj ReducedWords.xLetter s)
  | .m11, (r, s) => (r, wordConj ReducedWords.XLetter s)
  | .m12, (r, s) => (r, wordConj ReducedWords.yLetter s)
  | .m13, (r, s) => (r, wordConj ReducedWords.YLetter s)

def groupStep : Move → GroupState → GroupState
  | .m0, (r, s) => (r⁻¹, s)
  | .m1, (r, s) => (r, s⁻¹)
  | .m2, (r, s) => (r * s, s)
  | .m3, (r, s) => (r * s⁻¹, s)
  | .m4, (r, s) => (r, s * r)
  | .m5, (r, s) => (r, s * r⁻¹)
  | .m6, (r, s) => (Verify.x * r * Verify.X, s)
  | .m7, (r, s) => (Verify.X * r * Verify.x, s)
  | .m8, (r, s) => (Verify.y * r * Verify.Y, s)
  | .m9, (r, s) => (Verify.Y * r * Verify.y, s)
  | .m10, (r, s) => (r, Verify.x * s * Verify.X)
  | .m11, (r, s) => (r, Verify.X * s * Verify.x)
  | .m12, (r, s) => (r, Verify.y * s * Verify.Y)
  | .m13, (r, s) => (r, Verify.Y * s * Verify.y)

def wordRun : List Move → WordState → WordState
  | [], w => w
  | m :: ms, w => wordRun ms (wordStep m w)

def groupRun : List Move → GroupState → GroupState
  | [], s => s
  | m :: ms, s => groupRun ms (groupStep m s)

def ReducedState (w : WordState) : Prop :=
  FreeGroup.IsReduced w.1 ∧ FreeGroup.IsReduced w.2

def embed : ROperationConnection.Move → Move
  | .m2 => .m2 | .m3 => .m3 | .m4 => .m4 | .m5 => .m5
  | .m6 => .m6 | .m8 => .m8 | .m10 => .m10 | .m13 => .m13

def initialWords (n : ℕ) : WordState :=
  ([ReducedWords.XLetter] ++ List.replicate n ReducedWords.yLetter ++
      [ReducedWords.xLetter] ++ List.replicate (n + 1) ReducedWords.YLetter,
    [ReducedWords.xLetter] ++ List.replicate n ReducedWords.YLetter)

def branchMoves (J K F : List ROperationConnection.Move)
    (b : ROperationConnection.Critical) : List Move :=
  ([ROperationConnection.Move.m3, .m6, .m4] ++ J ++
    [ROperationConnection.Move.m4, .m3] ++ K ++
    ROperationConnection.criticalSeq b ++ F).map embed

theorem encodeLetter_inv (a : Letter) :
    encodeLetter (a.1, !a.2) = -encodeLetter a := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [encodeLetter]

theorem encode_invRev (w : Word) :
    encodeWord (FreeGroup.invRev w) = (encodeWord w).reverse.map (fun z : ℤ => -z) := by
  simp [encodeWord, FreeGroup.invRev, List.map_reverse, List.map_map,
    Function.comp_def, encodeLetter_inv]

theorem mk_wordConj (a : Letter) (w : Word) :
    FreeGroup.mk (wordConj a w) =
      FreeGroup.mk [a] * FreeGroup.mk w * (FreeGroup.mk [a])⁻¹ := by
  simp only [wordConj, FreeGroup.reduce.self, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]

theorem eval_wordStep (m : Move) (w : WordState) :
    evalState (wordStep m w) = groupStep m (evalState w) := by
  have hx : FreeGroup.mk [ReducedWords.xLetter] = Verify.x := rfl
  have hX : FreeGroup.mk [ReducedWords.XLetter] = Verify.X := rfl
  have hy : FreeGroup.mk [ReducedWords.yLetter] = Verify.y := rfl
  have hY : FreeGroup.mk [ReducedWords.YLetter] = Verify.Y := rfl
  rcases w with ⟨r, s⟩
  cases m <;> apply Prod.ext <;>
    simp only [wordStep, groupStep, evalState, mk_wordConj, FreeGroup.reduce.self,
      ← FreeGroup.inv_mk, ← FreeGroup.mul_mk, hx, hX, hy, hY]
  all_goals simp [Verify.X, Verify.Y]

theorem wordStep_reduced (m : Move) (w : WordState) (hw : ReducedState w) :
    ReducedState (wordStep m w) := by
  rcases w with ⟨r, s⟩
  rcases hw with ⟨hr, hs⟩
  have hreduce (L : Word) : FreeGroup.IsReduced (FreeGroup.reduce L) :=
    FreeGroup.IsReduced.of_reduce_eq FreeGroup.reduce.idem
  have hinv (L : Word) (hL : FreeGroup.IsReduced L) :
      FreeGroup.IsReduced (FreeGroup.invRev L) :=
    FreeGroup.IsReduced.of_reduce_eq (by rw [FreeGroup.reduce_invRev, hL.reduce_eq])
  cases m <;> dsimp only [wordStep, wordConj, ReducedState] <;> constructor
  all_goals first
    | exact hr
    | exact hs
    | exact hinv r hr
    | exact hinv s hs
    | exact hreduce _

theorem eval_wordRun (moves : List Move) (w : WordState) :
    evalState (wordRun moves w) = groupRun moves (evalState w) := by
  induction moves generalizing w with
  | nil => rfl
  | cons m ms ih =>
    simpa only [wordRun, groupRun, eval_wordStep] using ih (wordStep m w)

theorem wordRun_reduced (moves : List Move) (w : WordState) (hw : ReducedState w) :
    ReducedState (wordRun moves w) := by
  induction moves generalizing w with
  | nil => exact hw
  | cons m ms ih => exact ih (wordStep m w) (wordStep_reduced m w hw)

theorem wordRun_canonical (moves : List Move) (w : WordState) (hw : ReducedState w) :
    wordRun moves w =
      (FreeGroup.toWord (groupRun moves (evalState w)).1,
       FreeGroup.toWord (groupRun moves (evalState w)).2) := by
  have hr := wordRun_reduced moves w hw
  have he := eval_wordRun moves w
  apply Prod.ext
  · have h := congrArg Prod.fst he
    change FreeGroup.mk (wordRun moves w).1 = (groupRun moves (evalState w)).1 at h
    rw [← h, FreeGroup.toWord_mk, hr.1.reduce_eq]
  · have h := congrArg Prod.snd he
    change FreeGroup.mk (wordRun moves w).2 = (groupRun moves (evalState w)).2 at h
    rw [← h, FreeGroup.toWord_mk, hr.2.reduce_eq]

theorem embed_id (m : ROperationConnection.Move) :
    moveId (embed m) = ROperationConnection.moveId m := by
  cases m <;> rfl

theorem groupStep_embed (m : ROperationConnection.Move) (s : GroupState) :
    groupStep (embed m) s = ROperationConnection.step m s := by
  cases m <;> rfl

theorem groupRun_embed (moves : List ROperationConnection.Move) (s : GroupState) :
    groupRun (moves.map embed) s = ROperationConnection.run moves s := by
  induction moves generalizing s with
  | nil => rfl
  | cons m ms ih =>
    simpa only [List.map_cons, groupRun, ROperationConnection.run, groupStep_embed] using
      ih (ROperationConnection.step m s)

theorem eval_wordRun_embed (moves : List ROperationConnection.Move) (w : WordState) :
    evalState (wordRun (moves.map embed) w) = ROperationConnection.run moves (evalState w) := by
  rw [eval_wordRun, groupRun_embed]

theorem eval_initialWords (n : ℕ) : evalState (initialWords n) = ROperationConnection.initial n := by
  apply Prod.ext <;>
    simp only [initialWords, evalState, ROperationConnection.initial,
      ← FreeGroup.mul_mk, WordTools.mk_replicate]
  all_goals rfl

theorem wordBranch_eval (n : ℕ) (J K F : List ROperationConnection.Move)
    (b : ROperationConnection.Critical) :
    evalState (wordRun (branchMoves J K F b) (initialWords n)) =
      ROperationConnection.branch n J K F b := by
  rw [branchMoves, eval_wordRun_embed, eval_initialWords,
    ← ROperationConnection.branch_eq_run]

theorem wordBranch_excluded (n : ℕ) (J K F : List ROperationConnection.Move)
    (b : ROperationConnection.Critical) (hn : 6 ≤ n)
    (hJ : ∀ m ∈ J, m = .m2 ∨ m = .m6)
    (hK : ∀ m ∈ K, m = .m5 ∨ m = .m10)
    (hF : ∀ m ∈ F, m = .m2 ∨ m = .m6) :
    FreeGroup.mk (wordRun (branchMoves J K F b) (initialWords n)).2 ≠ Verify.y := by
  have he := congrArg Prod.snd (wordBranch_eval n J K F b)
  change FreeGroup.mk (wordRun (branchMoves J K F b) (initialWords n)).2 =
    (ROperationConnection.branch n J K F b).2 at he
  rw [he]
  exact ROperationConnection.branch_excluded n J K F b hn hJ hK hF

end Verify.AtomicSemantics

#print axioms Verify.AtomicSemantics.encodeLetter_inv
#print axioms Verify.AtomicSemantics.encode_invRev
#print axioms Verify.AtomicSemantics.mk_wordConj
#print axioms Verify.AtomicSemantics.eval_wordStep
#print axioms Verify.AtomicSemantics.wordStep_reduced
#print axioms Verify.AtomicSemantics.eval_wordRun
#print axioms Verify.AtomicSemantics.wordRun_reduced
#print axioms Verify.AtomicSemantics.wordRun_canonical
#print axioms Verify.AtomicSemantics.embed_id
#print axioms Verify.AtomicSemantics.groupStep_embed
#print axioms Verify.AtomicSemantics.groupRun_embed
#print axioms Verify.AtomicSemantics.eval_wordRun_embed
#print axioms Verify.AtomicSemantics.eval_initialWords
#print axioms Verify.AtomicSemantics.wordBranch_eval
#print axioms Verify.AtomicSemantics.wordBranch_excluded

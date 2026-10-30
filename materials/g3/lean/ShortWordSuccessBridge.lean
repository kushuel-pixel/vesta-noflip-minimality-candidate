import ShortWordNormalize
import ShortWordMarkBound
import Verify.QGroup

/-! Original success supplies the existing canonical Trace and literal terminal.
NoFlip is explicit: inversion moves 0 and 1 are not discarded as conjugations.
Only necessary abelianized information is used; no converse success or edited
free-group success is asserted. -/
namespace Candidate.ShortWordSuccessBridge
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordMatrix
open Candidate.ShortWordNormalize Verify.QModel

abbrev Move := Verify.AtomicSemantics.Move

def NoFlip (ms : List Move) : Prop := ∀ m ∈ ms, m ≠ .m0 ∧ m ≠ .m1

def stateMat (s : Verify.AtomicSemantics.GroupState) : Mat :=
  !![(toQ s.1).a, (toQ s.1).b; (toQ s.2).a, (toQ s.2).b]

def moveMat : Move → Mat
  | .m0 => !![-1, 0; 0, 1]
  | .m1 => !![1, 0; 0, -1]
  | .m2 => A
  | .m3 => !![1, -1; 0, 1]
  | .m4 => L
  | .m5 => !![1, 0; -1, 1]
  | _ => 1

def runMat : List Move → Mat
  | [] => 1
  | m :: ms => runMat ms * moveMat m

theorem stateMat_step (m : Move) (s : Verify.AtomicSemantics.GroupState) :
    stateMat (Verify.AtomicSemantics.groupStep m s) = moveMat m * stateMat s := by
  rcases s with ⟨r,s⟩
  cases m <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [stateMat, moveMat, Verify.AtomicSemantics.groupStep, A, L,
      Verify.X, Verify.Y, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem stateMat_run (ms : List Move) (s : Verify.AtomicSemantics.GroupState) :
    stateMat (Verify.AtomicSemantics.groupRun ms s) = runMat ms * stateMat s := by
  induction ms generalizing s with
  | nil => simp [Verify.AtomicSemantics.groupRun, runMat]
  | cons m ms ih =>
    simp only [Verify.AtomicSemantics.groupRun, ih, stateMat_step, runMat, mul_assoc]

theorem stateMat_initial (n : ℕ) : stateMat (Verify.ROperationConnection.initial n) =
    !![0, -1; 1, -(n : ℤ)] := by
  simp [stateMat, Verify.ROperationConnection.initial, toQ_uFamily, toQ_vFamily]

theorem stateMat_target : stateMat (Verify.x,Verify.y) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [stateMat, qx, qy]

theorem success_matrix {ms : List Move} {n : ℕ}
    (hs : Verify.AtomicSemantics.groupRun ms (Verify.ROperationConnection.initial n) =
      (Verify.x,Verify.y)) : runMat ms = -H n := by
  have he := congrArg stateMat hs
  rw [stateMat_run, stateMat_initial, stateMat_target] at he
  have e00 := congrArg (fun z : Mat => z 0 0) he
  have e01 := congrArg (fun z : Mat => z 0 1) he
  have e10 := congrArg (fun z : Mat => z 1 0) he
  have e11 := congrArg (fun z : Mat => z 1 1) he
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext i j; fin_cases i <;> fin_cases j <;> simp [H] <;> nlinarith

def atomMat : Atom → Mat
  | .a => A
  | .invA => !![1, -1; 0, 1]
  | .invB => L
  | .b => !![1, 0; -1, 1]

def atomRun : List Atom → Mat
  | [] => 1
  | kind :: atoms => atomRun atoms * atomMat kind

theorem expandAtom_signed (k : ℕ) (kind : Atom) :
    SignedEq (tokenEval (expandAtom k kind)) (atomMat kind) := by
  cases kind <;> simp only [tokenEval, values, expandAtom, leafToken, List.map_cons,
    List.map_nil, eval, factorMat, mul_one, atomMat]
  · exact Or.inl pair_a
  · right; decide +kernel
  · exact Or.inr pair_l
  · left; decide +kernel

theorem numbered_expansion_signed (atoms : List Atom) (k : ℕ) :
    SignedEq (tokenEval (expandChronological (numberFrom k atoms))) (atomRun atoms) := by
  induction atoms generalizing k with
  | nil => exact SignedEq.refl _
  | cons kind atoms ih =>
    have he : expandChronological (numberFrom k (kind :: atoms)) =
        expandChronological (numberFrom (k+1) atoms) ++ expandAtom k kind := by
      simp [numberFrom, expandChronological]
    rw [he, tokenEval_append, atomRun]
    exact (ih (k+1)).mul (expandAtom_signed k kind)

theorem noFlip_run_extraction (ms : List Move) (hn : NoFlip ms) :
    runMat ms = atomRun (ms.filterMap nielsenAtom) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hm := hn m (by simp)
    have ht : NoFlip ms := by
      intro a ha; exact hn a (by simp [ha])
    rw [runMat, ih ht]
    cases m <;> simp_all [List.filterMap_cons, nielsenAtom, atomRun, moveMat, atomMat]

theorem success_expansion_signed {ms : List Move} {n : ℕ}
    (hn : NoFlip ms)
    (hs : Verify.AtomicSemantics.groupRun ms (Verify.ROperationConnection.initial n) =
      (Verify.x,Verify.y)) :
    SignedEq (tokenEval (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))))
      (H n) := by
  have he := numbered_expansion_signed (ms.filterMap nielsenAtom) 0
  rw [← noFlip_run_extraction ms hn, success_matrix hs] at he
  exact he.trans (Or.inr rfl)

/-- Main bridge. No Trace, normal-form, length, or n≥6 premise is assumed. -/
theorem group_success_trace_terminal {ms : List Move} {n : ℕ}
    (hn : NoFlip ms)
    (hs : Verify.AtomicSemantics.groupRun ms (Verify.ROperationConnection.initial n) =
      (Verify.x,Verify.y)) :
    ∃ rs h f, ShortWordDelete.Trace
      (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))) rs h f ∧
      values f = terminal n :=
  exists_terminal_trace (success_expansion_signed hn hs)

theorem word_success_trace_terminal {ms : List Move} {n : ℕ}
    (hn : NoFlip ms)
    (hs : Verify.AtomicSemantics.wordRun ms (Verify.AtomicSemantics.initialWords n) =
      ([Verify.ReducedWords.xLetter],[Verify.ReducedWords.yLetter])) :
    ∃ rs h f, ShortWordDelete.Trace
      (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))) rs h f ∧
      values f = terminal n := by
  apply group_success_trace_terminal hn
  have he := congrArg Verify.AtomicSemantics.evalState hs
  rw [Verify.AtomicSemantics.eval_wordRun, Verify.AtomicSemantics.eval_initialWords] at he
  exact he

theorem success_terminal_deletion {ms : List Move} {n : ℕ}
    (hn : NoFlip ms) (hn6 : 6 ≤ n)
    (hs : Verify.AtomicSemantics.groupRun ms (Verify.ROperationConnection.initial n) =
      (Verify.x,Verify.y))
    (hq : (ms.filterMap nielsenAtom).length = n + 5 ∨
      (ms.filterMap nielsenAtom).length = n + 3) :
    ∃ (rs : List Rule) (h : List Leaf) (f : List Token)
      (e : ℕ) (pre : List Atom) (kind : Atom) (post : List Atom),
      ShortWordDelete.Trace
        (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))) rs h f ∧
      values f = terminal n ∧ e < (ms.filterMap nielsenAtom).length ∧
      ms.filterMap nielsenAtom = pre ++ kind :: post ∧ pre.length = e ∧
      clean e h = true ∧ (kind = .a ∨ kind = .b) ∧
      ShortWordDelete.Trace (expandChronological (numberFrom 0 (pre ++ post))) rs
        (h.map (relabelLeaf e)) (eraseOwner e f) ∧
      values (eraseOwner e f) = terminal (n-1) := by
  obtain ⟨rs,h,f,ht,he⟩ := group_success_trace_terminal hn hs
  obtain ⟨e,pre,kind,post,helt,hlist,hlen,hclean,hkind,hedit,hend⟩ :=
    ShortWordMarkBound.exists_terminal_deletion hn6 ht he hq
  exact ⟨rs,h,f,e,pre,kind,post,ht,he,helt,hlist,hlen,hclean,hkind,hedit,hend⟩

end Candidate.ShortWordSuccessBridge

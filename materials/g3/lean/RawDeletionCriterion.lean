import ShortWordSuccessBridge

namespace Candidate.RawDeletionCriterion
open Verify.AtomicSemantics

def inverseMove : Move → Move
  | .m0 => .m0 | .m1 => .m1
  | .m2 => .m3 | .m3 => .m2 | .m4 => .m5 | .m5 => .m4
  | .m6 => .m7 | .m7 => .m6 | .m8 => .m9 | .m9 => .m8
  | .m10 => .m11 | .m11 => .m10 | .m12 => .m13 | .m13 => .m12

theorem inverse_step (m : Move) (s : GroupState) :
    groupStep (inverseMove m) (groupStep m s) = s := by
  rcases s with ⟨r,s⟩
  cases m <;> simp [inverseMove,groupStep,Verify.X,Verify.Y,mul_assoc]

theorem groupStep_injective (m : Move) : Function.Injective (groupStep m) := by
  intro s t h
  have he := congrArg (groupStep (inverseMove m)) h
  simpa only [inverse_step] using he

theorem groupRun_injective (ms : List Move) : Function.Injective (groupRun ms) := by
  induction ms with
  | nil => exact fun _ _ h => h
  | cons m ms ih => exact ih.comp (groupStep_injective m)

theorem groupRun_append (p s : List Move) (input : GroupState) :
    groupRun (p ++ s) input = groupRun s (groupRun p input) := by
  induction p generalizing input with
  | nil => rfl
  | cons m p ih => exact ih (groupStep m input)

/-- Exact criterion for literal deletion of one raw move, with suffix unchanged.
No Trace premise, bounded-length hypothesis, or existence claim is included. -/
theorem deletion_success_iff (p s : List Move) (m : Move)
    (oldInput newInput target : GroupState)
    (hs : groupRun (p ++ m :: s) oldInput = target) :
    groupRun (p ++ s) newInput = target ↔
      groupRun p newInput = groupStep m (groupRun p oldInput) := by
  rw [groupRun_append] at hs ⊢
  change groupRun s (groupStep m (groupRun p oldInput)) = target at hs
  constructor
  · intro h
    exact groupRun_injective s (h.trans hs.symm)
  · intro h
    rw [h]
    exact hs

theorem family_deletion_success_iff (p s : List Move) (m : Move) (n : ℕ)
    (hs : groupRun (p ++ m :: s) (Verify.ROperationConnection.initial n) =
      (Verify.x,Verify.y)) :
    groupRun (p ++ s) (Verify.ROperationConnection.initial (n-1)) =
      (Verify.x,Verify.y) ↔
    groupRun p (Verify.ROperationConnection.initial (n-1)) =
      groupStep m (groupRun p (Verify.ROperationConnection.initial n)) :=
  deletion_success_iff p s m _ _ _ hs

theorem m2_cut_condition (oldState newState : GroupState) :
    newState = groupStep .m2 oldState ↔
    newState.1 = oldState.1 * oldState.2 ∧ newState.2 = oldState.2 := by
  rcases oldState with ⟨r,s⟩
  rcases newState with ⟨u,v⟩
  simp [groupStep]

theorem m5_cut_condition (oldState newState : GroupState) :
    newState = groupStep .m5 oldState ↔
    newState.1 = oldState.1 ∧ newState.2 = oldState.2 * oldState.1⁻¹ := by
  rcases oldState with ⟨r,s⟩
  rcases newState with ⟨u,v⟩
  simp [groupStep]

end Candidate.RawDeletionCriterion

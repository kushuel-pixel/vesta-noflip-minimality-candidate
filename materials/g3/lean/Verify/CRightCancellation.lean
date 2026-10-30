import Verify.ReducedC

/-! The single right-boundary cancellation C*x -> C^R in fixed MR044.
C^R deletes the last X; this module certifies a literal one-step reduction.
It makes no claims about E, K, D, cyclic reduction, or exclusion. -/

namespace Verify.CRightCancellation

open ReducedWords ReducedC

/-- k complete u blocks followed by the explicit shortened tail X y^n x Y. -/
def cRightCore (n : ℕ) : ℕ → List Letter
  | 0 => [XLetter] ++ (List.replicate n yLetter ++ [xLetter, YLetter])
  | k + 1 => [XLetter] ++ (List.replicate n yLetter ++
      ([xLetter] ++ (List.replicate (n + 1) YLetter ++ cRightCore n k)))

def cRightWord (n t : ℕ) : List Letter := cRightCore n (t - 1)

theorem cCore_decompose (n k : ℕ) :
    cCore n k = cRightCore n k ++ [XLetter] := by
  induction k with
  | zero => simp [cCore, cRightCore, List.append_assoc]
  | succ k ih => simp only [cCore, cRightCore, ih, List.append_assoc]

theorem cWord_decompose (n t : ℕ) :
    cWord n t = cRightWord n t ++ [XLetter] := cCore_decompose n (t - 1)

theorem cRightWord_last (n t : ℕ) :
    (cRightWord n t).getLast? = some YLetter := by
  have h (k : ℕ) : (cRightCore n k).getLast? = some YLetter := by
    induction k with
    | zero => simp only [cRightCore, List.getLast?_append]; rfl
    | succ k ih => simp only [cRightCore, List.getLast?_append, ih]; rfl
  exact h (t - 1)

theorem cRightWord_length (n t : ℕ) :
    (cRightWord n t).length = (t - 1) * (2 * n + 3) + n + 3 := by
  have h := congrArg List.length (cWord_decompose n t)
  rw [cWord_length] at h
  simp only [List.length_append, List.length_cons, List.length_nil] at h
  omega

theorem cRightWord_reduced (n t : ℕ) (hn : 3 ≤ n) :
    FreeGroup.IsReduced (cRightWord n t) := by
  have h := cWord_reduced n t hn
  rw [cWord_decompose] at h
  exact List.IsChain.left_of_append h

/-- Exactly one permitted inverse-pair deletion on the literal input, before group evaluation. -/
theorem cRight_cancel_step (n t : ℕ) :
    FreeGroup.Red.Step (cWord n t ++ [xLetter]) (cRightWord n t) := by
  rw [cWord_decompose, List.append_assoc]
  simpa using (FreeGroup.Red.Step.not (L₁ := cRightWord n t) (L₂ := [])
    (x := (0 : Fin 2)) (b := false))

/-- The appended input loses two letters; this is a list-step count, not a group guess. -/
theorem cRight_cancel_length (n t : ℕ) :
    (cRightWord n t).length + 2 = (cWord n t ++ [xLetter]).length :=
  (cRight_cancel_step n t).length

theorem mk_cRightWord (n t : ℕ) (hn : 3 ≤ n) (ht : 1 ≤ t) :
    FreeGroup.mk (cRightWord n t) =
      (ResearchWords.uFamily n ^ t * (ResearchWords.vFamily n)⁻¹) * Verify.x := by
  have hs : FreeGroup.mk (cWord n t ++ [xLetter]) =
      FreeGroup.mk (cRightWord n t) := Quot.sound (cRight_cancel_step n t)
  rw [← hs, ← FreeGroup.mul_mk, mk_cWord n t hn ht]
  rfl

theorem cRight_toWord (n t : ℕ) (hn : 3 ≤ n) (ht : 1 ≤ t) :
    FreeGroup.toWord ((ResearchWords.uFamily n ^ t *
      (ResearchWords.vFamily n)⁻¹) * Verify.x) = cRightWord n t :=
  (WordTools.word_certificate (mk_cRightWord n t hn ht) (cRightWord_reduced n t hn)).1

theorem cRight_norm (n t : ℕ) (hn : 3 ≤ n) (ht : 1 ≤ t) :
    FreeGroup.norm ((ResearchWords.uFamily n ^ t *
      (ResearchWords.vFamily n)⁻¹) * Verify.x) =
        (t - 1) * (2 * n + 3) + n + 3 := by
  simp only [FreeGroup.norm, cRight_toWord n t hn ht, cRightWord_length]

end Verify.CRightCancellation

#print axioms Verify.CRightCancellation.cCore_decompose
#print axioms Verify.CRightCancellation.cWord_decompose
#print axioms Verify.CRightCancellation.cRightWord_last
#print axioms Verify.CRightCancellation.cRightWord_length
#print axioms Verify.CRightCancellation.cRightWord_reduced
#print axioms Verify.CRightCancellation.cRight_cancel_step
#print axioms Verify.CRightCancellation.cRight_cancel_length
#print axioms Verify.CRightCancellation.mk_cRightWord
#print axioms Verify.CRightCancellation.cRight_toWord
#print axioms Verify.CRightCancellation.cRight_norm

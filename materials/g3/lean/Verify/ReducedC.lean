import Verify.ReducedWords

/-! Literal free reduction and norm for C_t = u_n^t v_n^-1, n >= 3, t >= 1.
Only the local word identity is used; no exclusion or operation bound is assumed. -/

namespace Verify.ReducedC

open ReducedWords

/-- k full u blocks followed by X y^n x Y X; k=0 has no full block. -/
def cCore (n : ℕ) : ℕ → List Letter
  | 0 => [XLetter] ++ (List.replicate n yLetter ++ [xLetter, YLetter, XLetter])
  | k + 1 => [XLetter] ++ (List.replicate n yLetter ++
      ([xLetter] ++ (List.replicate (n + 1) YLetter ++ cCore n k)))

/-- The displayed C word. Its relation to C_t is asserted only when t >= 1. -/
def cWord (n t : ℕ) : List Letter := cCore n (t - 1)

theorem mk_cCore (n k : ℕ) :
    FreeGroup.mk (cCore n k) = ResearchWords.uFamily n ^ k *
      Verify.X * Verify.y ^ n * Verify.x * Verify.Y * Verify.X := by
  induction k with
  | zero =>
    simp only [cCore, ← FreeGroup.mul_mk, WordTools.mk_replicate, pow_zero, one_mul]
    change Verify.X * (Verify.y ^ n * (Verify.x * Verify.Y * Verify.X)) = _
    simp only [mul_assoc]
  | succ k ih =>
    simp only [cCore, ← FreeGroup.mul_mk, WordTools.mk_replicate]
    change Verify.X * (Verify.y ^ n * (Verify.x *
      (Verify.Y ^ (n + 1) * FreeGroup.mk (cCore n k)))) = _
    rw [ih, pow_succ' (ResearchWords.uFamily n) k]
    simp only [ResearchWords.uFamily, mul_assoc]

theorem cCore_length (n k : ℕ) :
    (cCore n k).length = k * (2 * n + 3) + n + 4 := by
  induction k with
  | zero => simp [cCore]
  | succ k ih =>
    simp only [cCore, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate, ih]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem cCore_reduced (n k : ℕ) (hn : 3 ≤ n) :
    FreeGroup.IsReduced (cCore n k) := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  induction k with
  | zero =>
    have htail : FreeGroup.IsReduced [xLetter, YLetter, XLetter] := by
      unfold FreeGroup.IsReduced
      decide
    have hy := WordTools.reduced_replicate_append yLetter (m + 1) htail
      (by simp [xLetter])
    exact List.IsChain.cons hy (by simp [List.replicate_succ, XLetter, yLetter])
  | succ k ih =>
    have hY := WordTools.reduced_replicate_append YLetter (m + 1 + 1) ih
      (by cases k <;> simp [cCore, YLetter, XLetter])
    have hx : FreeGroup.IsReduced (xLetter ::
        (List.replicate (m + 1 + 1) YLetter ++ cCore (m + 1) k)) :=
      List.IsChain.cons hY (by simp [List.replicate_succ, YLetter])
    have hy := WordTools.reduced_replicate_append yLetter (m + 1) hx
      (by simp [xLetter])
    exact List.IsChain.cons hy (by simp [List.replicate_succ, yLetter])

theorem mk_cWord (n t : ℕ) (hn : 3 ≤ n) (ht : 1 ≤ t) :
    FreeGroup.mk (cWord n t) = ResearchWords.uFamily n ^ t *
      (ResearchWords.vFamily n)⁻¹ := by
  exact (mk_cCore n (t - 1)).trans (ResearchWords.c_expansion n t hn ht).symm

theorem cWord_length (n t : ℕ) :
    (cWord n t).length = (t - 1) * (2 * n + 3) + n + 4 :=
  cCore_length n (t - 1)

theorem cWord_reduced (n t : ℕ) (hn : 3 ≤ n) :
    FreeGroup.IsReduced (cWord n t) := cCore_reduced n (t - 1) hn

theorem c_toWord (n t : ℕ) (hn : 3 ≤ n) (ht : 1 ≤ t) :
    FreeGroup.toWord (ResearchWords.uFamily n ^ t *
      (ResearchWords.vFamily n)⁻¹) = cWord n t :=
  (WordTools.word_certificate (mk_cWord n t hn ht) (cWord_reduced n t hn)).1

theorem c_norm (n t : ℕ) (hn : 3 ≤ n) (ht : 1 ≤ t) :
    FreeGroup.norm (ResearchWords.uFamily n ^ t *
      (ResearchWords.vFamily n)⁻¹) = (t - 1) * (2 * n + 3) + n + 4 := by
  simp only [FreeGroup.norm, c_toWord n t hn ht, cWord_length]

end Verify.ReducedC

#print axioms Verify.ReducedC.mk_cCore
#print axioms Verify.ReducedC.cCore_length
#print axioms Verify.ReducedC.cCore_reduced
#print axioms Verify.ReducedC.mk_cWord
#print axioms Verify.ReducedC.cWord_length
#print axioms Verify.ReducedC.cWord_reduced
#print axioms Verify.ReducedC.c_toWord
#print axioms Verify.ReducedC.c_norm

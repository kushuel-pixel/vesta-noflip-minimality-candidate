import Verify.ResearchWords

/-! Free reduction and length of the fixed MR helper B. This module uses the
Mathlib signed-letter representation (generator, true=positive/false=inverse).
Only free reduction is certified; no cyclic reduction or operation bound is claimed. -/

namespace Verify.WordTools

/-- Evaluation of a repeated signed-letter block, using the existing quotient API. -/
theorem mk_replicate {α : Type*} (a : α × Bool) (n : ℕ) :
    FreeGroup.mk (List.replicate n a) = (FreeGroup.mk [a]) ^ n := by
  rw [FreeGroup.pow_mk, List.flatten_replicate_singleton]

/-- A homogeneous block can be prepended when its only new boundary is safe. -/
theorem reduced_replicate_append {α : Type*} (a : α × Bool) (n : ℕ)
    {L : List (α × Bool)} (hL : FreeGroup.IsReduced L)
    (hboundary : ∀ b ∈ L.head?, a.1 = b.1 → a.2 = b.2) :
    FreeGroup.IsReduced (List.replicate n a ++ L) := by
  induction n with
  | zero => simpa using hL
  | succ n ih =>
    cases n with
    | zero => simpa [FreeGroup.IsReduced] using (List.IsChain.cons hL hboundary)
    | succ k =>
      change FreeGroup.IsReduced (a :: a :: (List.replicate k a ++ L))
      exact FreeGroup.isReduced_cons_cons.mpr ⟨by intro _; rfl, ih⟩

/-- A representation plus reducedness yields the canonical word and its norm. -/
theorem word_certificate {α : Type*} [DecidableEq α]
    {L : List (α × Bool)} {g : FreeGroup α}
    (hmk : FreeGroup.mk L = g) (hred : FreeGroup.IsReduced L) :
    FreeGroup.toWord g = L ∧ FreeGroup.norm g = L.length := by
  have hw : FreeGroup.toWord g = L := by
    rw [← hmk, FreeGroup.toWord_mk, hred.reduce_eq]
  exact ⟨hw, by simp only [FreeGroup.norm, hw]⟩

end Verify.WordTools

namespace Verify.ReducedWords

abbrev Letter := Fin 2 × Bool
abbrev xLetter : Letter := (0, true)
abbrev yLetter : Letter := (1, true)
abbrev XLetter : Letter := (0, false)
abbrev YLetter : Letter := (1, false)

/-- The literal displayed word x Y^n X y^n x Y X, with no reduction performed. -/
def bWord (n : ℕ) : List Letter :=
  [xLetter] ++ (List.replicate n YLetter ++
    ([XLetter] ++ (List.replicate n yLetter ++ [xLetter, YLetter, XLetter])))

/-- The literal list evaluates to the existing conjugation expression. -/
theorem mk_bWord (n : ℕ) (hn : 3 ≤ n) :
    FreeGroup.mk (bWord n) =
      ResearchWords.vFamily n * ResearchWords.uFamily n * (ResearchWords.vFamily n)⁻¹ := by
  calc
    _ = Verify.x * Verify.Y ^ n * Verify.X * Verify.y ^ n * Verify.x * Verify.Y * Verify.X := by
      simp only [bWord, ← FreeGroup.mul_mk, WordTools.mk_replicate]
      change Verify.x * (Verify.Y ^ n * (Verify.X * (Verify.y ^ n *
        (Verify.x * Verify.Y * Verify.X)))) = _
      simp only [mul_assoc]
    _ = _ := (ResearchWords.conj_family n hn).symm

/-- Literal length is counted before using any reducedness assertion. -/
theorem bWord_length (n : ℕ) : (bWord n).length = 2 * n + 5 := by
  simp only [bWord, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- All adjacent boundaries are safe, for the stated MR domain n >= 3. -/
theorem bWord_reduced (n : ℕ) (hn : 3 ≤ n) : FreeGroup.IsReduced (bWord n) := by
  have htail : FreeGroup.IsReduced [xLetter, YLetter, XLetter] := by
    unfold FreeGroup.IsReduced
    decide
  have hy := WordTools.reduced_replicate_append yLetter n htail (by simp [xLetter])
  have hn0 : n ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hX : FreeGroup.IsReduced (XLetter :: (List.replicate (k + 1) yLetter ++
      [xLetter, YLetter, XLetter])) :=
    List.IsChain.cons hy (by simp [List.replicate_succ, XLetter, yLetter])
  have hY := WordTools.reduced_replicate_append YLetter (k + 1) hX
    (by simp [YLetter, XLetter])
  exact List.IsChain.cons hY (by simp [List.replicate_succ, xLetter, YLetter])

/-- Canonical reduced word, established using both representation and reducedness. -/
theorem b_toWord (n : ℕ) (hn : 3 ≤ n) :
    FreeGroup.toWord (ResearchWords.vFamily n * ResearchWords.uFamily n *
      (ResearchWords.vFamily n)⁻¹) = bWord n :=
  (WordTools.word_certificate (mk_bWord n hn) (bWord_reduced n hn)).1

/-- Free-word norm equals the original MR length 2n+5; not a cyclic length. -/
theorem b_norm (n : ℕ) (hn : 3 ≤ n) :
    FreeGroup.norm (ResearchWords.vFamily n * ResearchWords.uFamily n *
      (ResearchWords.vFamily n)⁻¹) = 2 * n + 5 := by
  simp only [FreeGroup.norm, b_toWord n hn, bWord_length]

/-- The same three helpers certify a separate small word y^2*x. -/
theorem small_example_norm : FreeGroup.norm (Verify.y ^ 2 * Verify.x) = 3 := by
  have hred : FreeGroup.IsReduced (List.replicate 2 yLetter ++ [xLetter]) :=
    WordTools.reduced_replicate_append yLetter 2 FreeGroup.IsReduced.singleton
      (by simp [xLetter])
  have hmk : FreeGroup.mk (List.replicate 2 yLetter ++ [xLetter]) =
      Verify.y ^ 2 * Verify.x := by
    rw [← FreeGroup.mul_mk, WordTools.mk_replicate]
    rfl
  simpa using (WordTools.word_certificate hmk hred).2

end Verify.ReducedWords

#print axioms Verify.WordTools.mk_replicate
#print axioms Verify.WordTools.reduced_replicate_append
#print axioms Verify.WordTools.word_certificate
#print axioms Verify.ReducedWords.mk_bWord
#print axioms Verify.ReducedWords.bWord_length
#print axioms Verify.ReducedWords.bWord_reduced
#print axioms Verify.ReducedWords.b_toWord
#print axioms Verify.ReducedWords.b_norm
#print axioms Verify.ReducedWords.small_example_norm

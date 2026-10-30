import Verify.Basic

/-!
# Research helper words as group elements

This module formalizes the prefix identity in Mathematics 044, Section 2 (1),
the helper expansions in Section 3.1 (8), and an algebraic consequence of the
formula E⁻¹ = C⁻¹ B⁻¹ stated after Section 2 (2). The initial words are also fixed
by Mathematics 045 / L022-NF2. The MR domain `n >= 3` is retained, along with
`t >= 1` for C and the projected bound `i + j <= n - 3` for E's inverse.
No claims about reduced words, lengths, operation sequences, or exclusion are made.

Source: `ACC_MATH_044_MR_LOOP_001_RESULT_2026-10-20.md`, Sections 2 (1), text after (2), 3.1 (8).
Current research scope: `ACC_MATH_045_NF2_INTEGRATION_LOOP_001_ENTRY_2026-10-20.md`.
-/

namespace Verify.ResearchWords

/-- The initial first word `u_n = X y^n x Y^(n+1)`. -/
def uFamily (n : ℕ) : Verify.F := Verify.X * Verify.y ^ n * Verify.x * Verify.Y ^ (n + 1)

/-- The initial second word `v_n = x Y^n`. -/
def vFamily (n : ℕ) : Verify.F := Verify.x * Verify.Y ^ n

/-- The family recovers the existing first word at `n = 3`. -/
theorem uFamily_three : uFamily 3 = Verify.u := by
  rfl

/-- The family recovers the existing second word at `n = 3`. -/
theorem vFamily_three : vFamily 3 = Verify.v := by
  rfl

/-- The group equality for the MR helper word `B`, in its stated research domain. -/
theorem conj_family (n : ℕ) (_hn : 3 ≤ n) :
    vFamily n * uFamily n * (vFamily n)⁻¹ =
      Verify.x * Verify.Y ^ n * Verify.X * Verify.y ^ n * Verify.x * Verify.Y * Verify.X := by
  simp [uFamily, vFamily, Verify.X, Verify.Y, pow_succ', mul_assoc]

/-- The general theorem specializes to the exact statement of `Verify.conj_example`. -/
theorem conj_family_three :
    Verify.v * Verify.u * Verify.v⁻¹ =
      Verify.x * Verify.Y ^ 3 * Verify.X * Verify.y ^ 3 * Verify.x * Verify.Y * Verify.X := by
  simpa only [uFamily_three, vFamily_three] using conj_family 3 (by decide)

/-- The original proof also gives the same family statement at `n = 3`. -/
theorem conj_example_as_family :
    vFamily 3 * uFamily 3 * (vFamily 3)⁻¹ =
      Verify.x * Verify.Y ^ 3 * Verify.X * Verify.y ^ 3 * Verify.x * Verify.Y * Verify.X := by
  simpa only [uFamily_three, vFamily_three] using Verify.conj_example

/-- MR044-SYSTEM (1): the pure-prefix product, as a group equality. -/
theorem prefix_product (n i j : ℕ) (_hn : 3 ≤ n) :
    (uFamily n ^ (i + 1) * (vFamily n)⁻¹) *
      (vFamily n * uFamily n * (vFamily n)⁻¹) ^ j =
        uFamily n ^ (i + j + 1) * (vFamily n)⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ (vFamily n * uFamily n * (vFamily n)⁻¹), ← mul_assoc, ih]
    simp only [mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc, ← pow_succ]
    rfl

/-- MR044-WORD-TABLE (8): C's expansion, without reduced-word claims. -/
theorem c_expansion (n t : ℕ) (_hn : 3 ≤ n) (ht : 1 ≤ t) :
    uFamily n ^ t * (vFamily n)⁻¹ =
      uFamily n ^ (t - 1) * Verify.X * Verify.y ^ n * Verify.x * Verify.Y * Verify.X := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [Nat.succ_sub_one, pow_succ]
  simp [uFamily, vFamily, Verify.X, Verify.Y, pow_succ', mul_assoc]

/-- MR044-SYSTEM: E's inverse after the pure prefix, using (1), (8), and the
inverse formula following (2).
The projected bound from `i + j + k + ℓ = n - 3` is retained. This is only a
group-element identity, without a claim about operation states or reduced words. -/
theorem e_prefix_inverse_expansion (n i j : ℕ) (hn : 3 ≤ n)
    (_hij : i + j ≤ n - 3) :
    ((vFamily n * uFamily n * (vFamily n)⁻¹) *
      ((uFamily n ^ (i + 1) * (vFamily n)⁻¹) *
        (vFamily n * uFamily n * (vFamily n)⁻¹) ^ j))⁻¹ =
      (uFamily n ^ (i + j) * Verify.X * Verify.y ^ n * Verify.x * Verify.Y * Verify.X)⁻¹ *
        (Verify.x * Verify.Y ^ n * Verify.X * Verify.y ^ n * Verify.x * Verify.Y * Verify.X)⁻¹ := by
  rw [prefix_product n i j hn, mul_inv_rev,
    c_expansion n (i + j + 1) hn (Nat.succ_le_succ (Nat.zero_le (i + j))),
    conj_family n hn]
  simp only [Nat.add_sub_cancel]

end Verify.ResearchWords

#print axioms Verify.ResearchWords.uFamily_three
#print axioms Verify.ResearchWords.vFamily_three
#print axioms Verify.ResearchWords.conj_family
#print axioms Verify.ResearchWords.conj_family_three
#print axioms Verify.ResearchWords.conj_example_as_family

#print axioms Verify.ResearchWords.prefix_product
#print axioms Verify.ResearchWords.c_expansion

#print axioms Verify.ResearchWords.e_prefix_inverse_expansion

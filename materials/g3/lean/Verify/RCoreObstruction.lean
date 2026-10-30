import Verify.CRightCancellation

/-! The final group obstruction in fixed062 §8 / reviewed063 F063-003.
This certifies no conjugator for y*x^2*y*X^2 and y^2, not the operation-to-word
derivation or the full R/G_n exclusion. -/

namespace Verify.WordTools

/-- A cyclically reduced literal word has no cancellation between repeated copies. -/
theorem norm_pow_of_cyclicallyReduced {α : Type*} [DecidableEq α]
    (L : List (α × Bool)) (h : FreeGroup.IsCyclicallyReduced L) (m : ℕ) :
    FreeGroup.norm (FreeGroup.mk L ^ m) = m * L.length := by
  have hred := (h.flatten_replicate m).isReduced
  have hmk : FreeGroup.mk (List.replicate m L).flatten = FreeGroup.mk L ^ m :=
    (FreeGroup.pow_mk m).symm
  simpa using (word_certificate hmk hred).2

end Verify.WordTools

namespace Verify.RCoreObstruction

open ReducedWords

def rP : Verify.F := Verify.x ^ 2 * Verify.y * Verify.X ^ 2
def rStem : Verify.F := Verify.y * rP
def rWord : List Letter := [yLetter, xLetter, xLetter, yLetter, XLetter, XLetter]

theorem mk_rWord : FreeGroup.mk rWord = rStem := by rfl

theorem rWord_cyclicallyReduced : FreeGroup.IsCyclicallyReduced rWord := by
  unfold FreeGroup.IsCyclicallyReduced FreeGroup.IsReduced rWord
  decide

theorem r_toWord : FreeGroup.toWord rStem = rWord :=
  (WordTools.word_certificate mk_rWord rWord_cyclicallyReduced.isReduced).1

theorem r_norm : FreeGroup.norm rStem = 6 := by
  rw [FreeGroup.norm, r_toWord]
  rfl

theorem r_pow_norm (m : ℕ) : FreeGroup.norm (rStem ^ m) = 6 * m := by
  have h := WordTools.norm_pow_of_cyclicallyReduced rWord rWord_cyclicallyReduced m
  rw [mk_rWord] at h
  simpa [rWord, Nat.mul_comm] using h

theorem ysq_pow_norm (m : ℕ) : FreeGroup.norm ((Verify.y ^ 2) ^ m) = 2 * m := by
  rw [← pow_mul]
  exact FreeGroup.norm_of_pow (1 : Fin 2) (2 * m)

theorem no_r_conjugator (Q : Verify.F) :
    Q * rStem * Q⁻¹ ≠ Verify.y ^ 2 := by
  intro h
  let m := FreeGroup.norm Q + 1
  have hp : Q * rStem ^ m * Q⁻¹ = (Verify.y ^ 2) ^ m := by
    simpa only [conj_pow] using congrArg (fun z : Verify.F => z ^ m) h
  have hb : rStem ^ m = Q⁻¹ * (Verify.y ^ 2) ^ m * Q := by
    calc
      _ = Q⁻¹ * (Q * rStem ^ m * Q⁻¹) * Q := by simp [mul_assoc]
      _ = _ := by rw [hp]
  have hle := (FreeGroup.norm_mul_le (Q⁻¹ * (Verify.y ^ 2) ^ m) Q).trans
    (Nat.add_le_add_right (FreeGroup.norm_mul_le Q⁻¹ ((Verify.y ^ 2) ^ m))
      (FreeGroup.norm Q))
  rw [← hb, r_pow_norm, ysq_pow_norm, FreeGroup.norm_inv_eq] at hle
  dsimp [m] at hle
  omega

end Verify.RCoreObstruction

#print axioms Verify.WordTools.norm_pow_of_cyclicallyReduced
#print axioms Verify.RCoreObstruction.mk_rWord
#print axioms Verify.RCoreObstruction.rWord_cyclicallyReduced
#print axioms Verify.RCoreObstruction.r_toWord
#print axioms Verify.RCoreObstruction.r_norm
#print axioms Verify.RCoreObstruction.r_pow_norm
#print axioms Verify.RCoreObstruction.ysq_pow_norm
#print axioms Verify.RCoreObstruction.no_r_conjugator

import ShortWordDelete
import ShortWordRecovery

/-! Integer matrix interpretation of the existing factor alphabet.
Equality up to central sign is a relation, never an assumed presentation theorem. -/
namespace Candidate.ShortWordMatrix
open Candidate.ShortWordDelete Candidate.ShortWordRecovery

abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

def S : Mat := !![0, -1; 1, 0]
def R : Mat := !![0, 1; -1, -1]
def Ri : Mat := !![-1, -1; 1, 0]
def A : Mat := !![1, 1; 0, 1]
def L : Mat := !![1, 0; 1, 1]
def H (n : ℕ) : Mat := !![(n : ℤ), -1; 1, 0]
def U (n : ℕ) : Mat := !![1, (n : ℤ); 0, 1]

def SignedEq (a b : Mat) : Prop := a = b ∨ a = -b

theorem SignedEq.refl (a : Mat) : SignedEq a a := Or.inl rfl

theorem SignedEq.symm {a b : Mat} (h : SignedEq a b) : SignedEq b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

theorem SignedEq.trans {a b c : Mat} (h : SignedEq a b) (k : SignedEq b c) :
    SignedEq a c := by
  rcases h with rfl | rfl <;> rcases k with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

theorem SignedEq.mul {a b c d : Mat} (h : SignedEq a b) (k : SignedEq c d) :
    SignedEq (a * c) (b * d) := by
  rcases h with rfl | rfl <;> rcases k with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (mul_neg _ _)
  · exact Or.inr (neg_mul _ _)
  · exact Or.inl (neg_mul_neg _ _)

def factorMat : Factor → Mat
  | .sigma => S | .rho => R | .rhoInv => Ri

def eval : List Factor → Mat
  | [] => 1
  | a :: w => factorMat a * eval w

@[simp] theorem eval_nil : eval [] = 1 := rfl
@[simp] theorem eval_cons (a : Factor) (w : List Factor) :
    eval (a :: w) = factorMat a * eval w := rfl

@[simp] theorem eval_append (u v : List Factor) : eval (u ++ v) = eval u * eval v := by
  induction u with
  | nil => simp [eval]
  | cons a u ih => simp [eval, ih, mul_assoc]

def tokenEval (w : List Token) : Mat := eval (values w)

@[simp] theorem tokenEval_append (u v : List Token) :
    tokenEval (u ++ v) = tokenEval u * tokenEval v := by
  simp [tokenEval, values]

theorem pair_t : S * S = -(1 : Mat) := by decide +kernel
theorem pair_u : Ri * Ri = R := by decide +kernel
theorem pair_v : R * R = Ri := by decide +kernel
theorem pair_z₁ : R * Ri = 1 := by decide +kernel
theorem pair_z₂ : Ri * R = 1 := by decide +kernel
theorem pair_a : S * R = A := by decide +kernel
theorem pair_l : S * Ri = -L := by decide +kernel

theorem legal_signed {r : Rule} {a b : Token} (h : Legal r a b) :
    SignedEq (tokenEval [a,b]) (tokenEval (output r a b)) := by
  rcases h with ⟨_, _, h⟩
  cases r with
  | t =>
    rcases h with ⟨ha,hb⟩
    simp only [tokenEval, values, List.map_cons, List.map_nil, eval, ha, hb,
      factorMat, mul_one, output]
    exact Or.inr pair_t
  | u =>
    rcases h with ⟨ha,hb⟩
    simp only [tokenEval, values, List.map_cons, List.map_nil, eval, ha, hb,
      factorMat, mul_one, output]
    exact Or.inl pair_u
  | v =>
    rcases h with ⟨ha,hb⟩
    simp only [tokenEval, values, List.map_cons, List.map_nil, eval, ha, hb,
      factorMat, mul_one, output]
    exact Or.inl pair_v
  | z =>
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simp only [tokenEval, values, List.map_cons, List.map_nil, eval, ha, hb,
        factorMat, mul_one, output]
      exact Or.inl pair_z₁
    · simp only [tokenEval, values, List.map_cons, List.map_nil, eval, ha, hb,
        factorMat, mul_one, output]
      exact Or.inl pair_z₂

theorem trace_signed {w f : List Token} {rs : List Rule} {h : List Leaf}
    (ht : ShortWordDelete.Trace w rs h f) : SignedEq (tokenEval w) (tokenEval f) := by
  induction ht with
  | nil w => exact SignedEq.refl _
  | step p s a b r legal tail ih =>
    have hp := (SignedEq.refl (tokenEval p)).mul (legal_signed legal)
    have hs := hp.mul (SignedEq.refl (tokenEval s))
    have hs' : SignedEq (tokenEval (p ++ [a,b] ++ s))
        (tokenEval (p ++ output r a b ++ s)) := by
      simpa only [tokenEval_append, mul_assoc] using hs
    exact hs'.trans ih

theorem eval_terminal (n : ℕ) : eval (terminal n) = H n := by
  induction n with
  | zero => simp [terminal, eval, factorMat, H, S]
  | succ n ih =>
    simp only [terminal, eval_cons, factorMat, ← mul_assoc, pair_a, ih]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, H, Matrix.mul_apply, Fin.sum_univ_two]

end Candidate.ShortWordMatrix

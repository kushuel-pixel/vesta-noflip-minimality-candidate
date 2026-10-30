import ShortTraceDepth

namespace Candidate.NegativeNielsenCount
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordMatrix
open Candidate.ShortWordCounts Candidate.ShortWordSuccessBridge

def negativeAtom : Atom → ℕ
  | .invA | .invB => 1
  | _ => 0

def negativeCount (atoms : List Atom) : ℕ := (atoms.map negativeAtom).sum

def rhoCharge (w : List Token) : ℤ :=
  (w.map (fun t => match t.value with | .sigma => 0 | .rho => 1 | .rhoInv => -1)).sum

@[simp] theorem rhoCharge_append (p s : List Token) :
    rhoCharge (p ++ s) = rhoCharge p + rhoCharge s := by simp [rhoCharge]

theorem trace_rho_charge {w f : List Token} {rs : List Rule} {h : List Leaf}
    (ht : Trace w rs h f) :
    rhoCharge f = rhoCharge w + 3*(rs.count .u : ℤ) - 3*(rs.count .v : ℤ) := by
  induction ht with
  | nil w => simp
  | step p s a b r hl tail ih =>
    cases r <;> simp only [Legal] at hl
    all_goals obtain ⟨_,_,hv⟩ := hl
    case t =>
      obtain ⟨ha,hb⟩ := hv
      simp [rhoCharge,output,ha,hb] at ih ⊢
      omega
    case u =>
      obtain ⟨ha,hb⟩ := hv
      simp [rhoCharge,output,ha,hb] at ih ⊢
      omega
    case v =>
      obtain ⟨ha,hb⟩ := hv
      simp [rhoCharge,output,ha,hb] at ih ⊢
      omega
    case z =>
      rcases hv with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
        simp [rhoCharge,output,ha,hb] at ih ⊢ <;> omega

theorem expansion_rho_charge (atoms : List Atom) (k : ℕ) :
    rhoCharge (expandChronological (numberFrom k atoms)) =
      (atoms.length : ℤ) - 2 * (negativeCount atoms : ℤ) := by
  induction atoms generalizing k with
  | nil => simp [numberFrom,expandChronological,rhoCharge,negativeCount]
  | cons a atoms ih =>
    have he : expandChronological (numberFrom k (a :: atoms)) =
        expandChronological (numberFrom (k+1) atoms) ++ expandAtom k a := by
      simp [numberFrom,expandChronological]
    rw [he,rhoCharge_append,ih]
    cases a <;> simp [expandAtom,rhoCharge,leafToken,negativeCount,negativeAtom] <;> omega

theorem terminal_rho_charge {f : List Token} {n : ℕ}
    (he : values f = terminal n) : rhoCharge f = n := by
  have hh : ∀ n, ((terminal n).map (fun v => match v with
      | Factor.sigma => (0:ℤ) | .rho => 1 | .rhoInv => -1)).sum = (n : ℤ) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [terminal,ih]; omega
  have := hh n
  rw [← he] at this
  simpa [values,rhoCharge,List.map_map,Function.comp_def] using this

theorem negative_trace_balance {atoms : List Atom} {n d : ℕ}
    {rs : List Rule} {h : List Leaf} {f : List Token}
    (ht : Trace (expandChronological (numberFrom 0 atoms)) rs h f)
    (he : values f = terminal n) (hq : atoms.length = n+d) :
    (negativeCount atoms : ℤ) + 3*(rs.count .v : ℤ) + 3*(rs.count .z : ℤ) = 2*(d:ℤ) := by
  have hb := numbered_balance ht he hq
  have hc := trace_rho_charge ht
  rw [expansion_rho_charge,terminal_rho_charge he,hq] at hc
  omega

theorem negative_count_zero_three_six {atoms : List Atom} {n : ℕ}
    {rs : List Rule} {h : List Leaf} {f : List Token}
    (ht : Trace (expandChronological (numberFrom 0 atoms)) rs h f)
    (he : values f = terminal n) (hq : atoms.length = n+3) :
    negativeCount atoms = 0 ∨ negativeCount atoms = 3 ∨ negativeCount atoms = 6 := by
  have := negative_trace_balance ht he hq
  omega

/-- Exact central sign, with no presentation theorem assumed. -/
def twist : ℕ → Mat → Mat
  | 0, m => m
  | k+1, m => -(twist k m)

theorem twist_add (a b : ℕ) (m : Mat) : twist (a+b) m = twist a (twist b m) := by
  induction a with
  | zero => simp [twist]
  | succ a ih => simp [Nat.succ_add,twist,ih]

theorem twist_mul_left (k : ℕ) (a b : Mat) : twist k a * b = twist k (a*b) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [twist,neg_mul,ih]

theorem twist_mul_right (k : ℕ) (a b : Mat) : a * twist k b = twist k (a*b) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [twist,mul_neg,ih]

theorem twist_mul (i j : ℕ) (a b : Mat) :
    twist i a * twist j b = twist (i+j) (a*b) := by
  rw [twist_mul_left,twist_mul_right,← twist_add]

theorem legal_exact_sign {r : Rule} {a b : Token} (hl : Legal r a b) :
    tokenEval [a,b] = twist (if r = .t then 1 else 0) (tokenEval (output r a b)) := by
  rcases hl with ⟨_,_,h⟩
  cases r with
  | t =>
    rcases h with ⟨ha,hb⟩
    simpa [tokenEval,values,eval,output,twist,ha,hb,factorMat] using pair_t
  | u =>
    rcases h with ⟨ha,hb⟩
    simpa [tokenEval,values,eval,output,twist,ha,hb,factorMat] using pair_u
  | v =>
    rcases h with ⟨ha,hb⟩
    simpa [tokenEval,values,eval,output,twist,ha,hb,factorMat] using pair_v
  | z =>
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa [tokenEval,values,eval,output,twist,ha,hb,factorMat] using pair_z₁
    · simpa [tokenEval,values,eval,output,twist,ha,hb,factorMat] using pair_z₂

theorem trace_exact_sign {w f : List Token} {rs : List Rule} {h : List Leaf}
    (ht : Trace w rs h f) : tokenEval w = twist (rs.count .t) (tokenEval f) := by
  induction ht with
  | nil w => rfl
  | step p s a b r hl tail ih =>
    simp only [tokenEval_append] at ih ⊢
    rw [legal_exact_sign hl,twist_mul_right,twist_mul_left]
    rw [ih,← twist_add]
    cases r <;> simp [Nat.add_comm]

theorem expandAtom_exact_sign (k : ℕ) (a : Atom) :
    tokenEval (expandAtom k a) = twist (negativeAtom a) (atomMat a) := by
  cases a <;> simp [tokenEval,values,expandAtom,leafToken,eval,factorMat,
    twist,negativeAtom,atomMat] <;> decide +kernel

theorem expansion_exact_sign (atoms : List Atom) (k : ℕ) :
    tokenEval (expandChronological (numberFrom k atoms)) =
      twist (negativeCount atoms) (atomRun atoms) := by
  induction atoms generalizing k with
  | nil => rfl
  | cons a atoms ih =>
    have he : expandChronological (numberFrom k (a :: atoms)) =
        expandChronological (numberFrom (k+1) atoms) ++ expandAtom k a := by
      simp [numberFrom,expandChronological]
    rw [he,tokenEval_append,ih,expandAtom_exact_sign,twist_mul]
    simp [negativeCount,atomRun,Nat.add_comm]

theorem matrix_endpoint_negative_zero_or_six {atoms : List Atom} {n : ℕ}
    (hq : atoms.length = n+3) (hend : atomRun atoms = -H n) :
    negativeCount atoms = 0 ∨ negativeCount atoms = 6 := by
  have hs : SignedEq (tokenEval (expandChronological (numberFrom 0 atoms))) (H n) :=
    (numbered_expansion_signed atoms 0).trans (by rw [hend]; exact Or.inr rfl)
  obtain ⟨rs,h,f,ht,he⟩ := Candidate.ShortWordNormalize.exists_terminal_trace hs
  rcases negative_count_zero_three_six ht he hq with hk | hk | hk
  · exact Or.inl hk
  · have hb := numbered_balance ht he hq
    have ht1 : rs.count .t = 1 := by omega
    have hsign := trace_exact_sign ht
    rw [expansion_exact_sign,hk,hend,ht1] at hsign
    have hterm : tokenEval f = H n := by rw [tokenEval,he,eval_terminal]
    rw [hterm] at hsign
    have hx := congrArg (fun m : Mat => m 0 1) hsign
    norm_num [twist,H] at hx
  · exact Or.inr hk

theorem success_negative_zero_or_six {ms : List Verify.AtomicSemantics.Move} {n : ℕ}
    (hno : NoFlip ms) (hq : (ms.filterMap nielsenAtom).length = n+3)
    (hend : Verify.AtomicSemantics.groupRun ms (Verify.ROperationConnection.initial n) =
      (Verify.x,Verify.y)) :
    negativeCount (ms.filterMap nielsenAtom) = 0 ∨
      negativeCount (ms.filterMap nielsenAtom) = 6 := by
  apply matrix_endpoint_negative_zero_or_six hq
  rw [← noFlip_run_extraction ms hno,success_matrix hend]

theorem negative_count_one_four_seven_ten {atoms : List Atom} {n : ℕ}
    {rs : List Rule} {h : List Leaf} {f : List Token}
    (ht : Trace (expandChronological (numberFrom 0 atoms)) rs h f)
    (he : values f = terminal n) (hq : atoms.length = n+5) :
    negativeCount atoms = 1 ∨ negativeCount atoms = 4 ∨
      negativeCount atoms = 7 ∨ negativeCount atoms = 10 := by
  have := negative_trace_balance ht he hq
  omega

theorem matrix_endpoint_negative_one_or_seven {atoms : List Atom} {n : ℕ}
    (hq : atoms.length = n+5) (hend : atomRun atoms = -H n) :
    negativeCount atoms = 1 ∨ negativeCount atoms = 7 := by
  have hs : SignedEq (tokenEval (expandChronological (numberFrom 0 atoms))) (H n) :=
    (numbered_expansion_signed atoms 0).trans (by rw [hend]; exact Or.inr rfl)
  obtain ⟨rs,h,f,ht,he⟩ := Candidate.ShortWordNormalize.exists_terminal_trace hs
  have hb := numbered_balance ht he hq
  have ht2 : rs.count .t = 2 := by omega
  have hsign := trace_exact_sign ht
  have hterm : tokenEval f = H n := by rw [tokenEval,he,eval_terminal]
  rw [expansion_exact_sign,hend,ht2,hterm] at hsign
  rcases negative_count_one_four_seven_ten ht he hq with hk | hk | hk | hk
  · exact Or.inl hk
  · rw [hk] at hsign
    have hx := congrArg (fun m : Mat => m 0 1) hsign
    norm_num [twist,H] at hx
  · exact Or.inr hk
  · rw [hk] at hsign
    have hx := congrArg (fun m : Mat => m 0 1) hsign
    norm_num [twist,H] at hx

theorem success_negative_one_or_seven {ms : List Verify.AtomicSemantics.Move} {n : ℕ}
    (hno : NoFlip ms) (hq : (ms.filterMap nielsenAtom).length = n+5)
    (hend : Verify.AtomicSemantics.groupRun ms (Verify.ROperationConnection.initial n) =
      (Verify.x,Verify.y)) :
    negativeCount (ms.filterMap nielsenAtom) = 1 ∨
      negativeCount (ms.filterMap nielsenAtom) = 7 := by
  apply matrix_endpoint_negative_one_or_seven hq
  rw [← noFlip_run_extraction ms hno,success_matrix hend]

theorem nplus3_negative_six_profile {atoms : List Atom} {n : ℕ}
    {rs : List Rule} {h : List Leaf} {f : List Token}
    (ht : Trace (expandChronological (numberFrom 0 atoms)) rs h f)
    (he : values f = terminal n) (hq : atoms.length = n+3)
    (hk : negativeCount atoms = 6) :
    rs.count .t = 1 ∧ rs.count .u = 3 ∧ rs.count .v = 0 ∧ rs.count .z = 0 := by
  have hb := numbered_balance ht he hq
  have hc := negative_trace_balance ht he hq
  rw [hk] at hc
  omega

theorem nplus3_negative_zero_profile {atoms : List Atom} {n : ℕ}
    {rs : List Rule} {h : List Leaf} {f : List Token}
    (ht : Trace (expandChronological (numberFrom 0 atoms)) rs h f)
    (he : values f = terminal n) (hq : atoms.length = n+3)
    (hk : negativeCount atoms = 0) :
    rs.count .t = 1 ∧
      ((rs.count .u = 1 ∧ rs.count .v = 2 ∧ rs.count .z = 0) ∨
       (rs.count .u = 0 ∧ rs.count .v = 1 ∧ rs.count .z = 1)) := by
  have hb := numbered_balance ht he hq
  have hc := negative_trace_balance ht he hq
  rw [hk] at hc
  omega

end Candidate.NegativeNielsenCount

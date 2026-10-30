import ShortWordDelete

/-! D2 local terminal-leaf recovery. The terminal is a literal factor list,
not an asserted PSL/SL evaluation. No free-group nonarrival or coverage. -/

namespace Candidate.ShortWordRecovery
open Candidate.ShortWordDelete

def values (w : List Token) : List Factor := w.map Token.value

def terminal : ℕ → List Factor
  | 0 => [.sigma]
  | n + 1 => .sigma :: .rho :: terminal n

theorem pair_prefix_iff {α : Type} (x y c : α) (w : List α) :
    [x,y] <+: c :: w ↔ x = c ∧ ∃ s, w = y :: s := by
  constructor
  · rintro ⟨s, h⟩
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact ⟨h.1, s, h.2.symm⟩
  · rintro ⟨rfl, s, rfl⟩
    exact ⟨s, rfl⟩

/-- Replacing a clean redex cannot disturb a protected adjacent pair. The
replacement may have length 0 or 1 (the lemma allows any replacement). -/
theorem protected_pair_step (e : ℕ) (x y a b : Token)
    (hx : clean e x.support = false) (hy : clean e y.support = false)
    (ha : clean e a.support = true) (hb : clean e b.support = true)
    (p s replacement : List Token)
    (hin : [x,y] <:+: p ++ [a,b] ++ s) :
    [x,y] <:+: p ++ replacement ++ s := by
  induction p with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.nil_append] at hin ⊢
    rcases List.infix_cons_iff.mp hin with hp | hin
    · have he := (pair_prefix_iff x y a _).mp hp
      have := congrArg (fun t : Token => clean e t.support) he.1
      rw [hx, ha] at this
      contradiction
    · rcases List.infix_cons_iff.mp hin with hp | hin
      · have he := (pair_prefix_iff x y b _).mp hp
        have := congrArg (fun t : Token => clean e t.support) he.1
        rw [hx, hb] at this
        contradiction
      · rcases hin with ⟨left, right, he⟩
        exact ⟨replacement ++ left, right, by
          simpa [List.append_assoc] using (congrArg (fun w => replacement ++ w) he)⟩
  | cons c p ih =>
    simp only [List.cons_append] at hin ⊢
    rcases List.infix_cons_iff.mp hin with hp | hin
    · obtain ⟨hxc, rest, he⟩ := (pair_prefix_iff x y c _).mp hp
      subst c
      cases p with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.nil_append] at he
        have hay : a = y := (List.cons.inj he).1
        have := congrArg (fun t : Token => clean e t.support) hay
        rw [ha, hy] at this
        contradiction
      | cons d p =>
        simp only [List.cons_append] at he
        have hdy : d = y := (List.cons.inj he).1
        subst d
        exact ⟨[], p ++ replacement ++ s, rfl⟩
    · exact List.infix_cons (ih hin)

theorem Trace.protected_pair {start finish : List Token} {rules : List Rule}
    {history : List Leaf} (ht : ShortWordDelete.Trace start rules history finish)
    (e : ℕ) (hu : clean e history = true) (x y : Token)
    (hx : clean e x.support = false) (hy : clean e y.support = false)
    (hin : [x,y] <:+: start) : [x,y] <:+: finish := by
  induction ht with
  | nil => exact hin
  | step p s a b r legal tail ih =>
    simp only [clean_append, Bool.and_eq_true] at hu
    obtain ⟨⟨ha,hb⟩,hh⟩ := hu
    exact ih hh (protected_pair_step e x y a b hx hy ha hb p s (output r a b) hin)

theorem expandChronological_append (pre post : List (ℕ × Atom)) :
    expandChronological (pre ++ post) =
      expandChronological post ++ expandChronological pre := by
  simp [expandChronological]

theorem original_block_infix (pre post : List (ℕ × Atom)) (e : ℕ) (kind : Atom) :
    expandAtom e kind <:+: expandChronological (pre ++ [(e,kind)] ++ post) := by
  refine ⟨expandChronological post, expandChronological pre, ?_⟩
  simp [expandChronological, List.append_assoc]

/-- Same two tokens, same singleton original leaves, not just equal factors. -/
theorem original_pair_survives (pre post : List (ℕ × Atom)) (e : ℕ) (kind : Atom)
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace
      (expandChronological (pre ++ [(e,kind)] ++ post)) rules history finish)
    (hu : clean e history = true) : expandAtom e kind <:+: finish := by
  have hi := original_block_infix pre post e kind
  cases kind <;>
    exact Trace.protected_pair ht e hu _ _ (by simp [leafToken, clean])
      (by simp [leafToken, clean]) hi

theorem terminal_no_inverse (n : ℕ) : Factor.rhoInv ∉ terminal n := by
  induction n with
  | zero => simp [terminal]
  | succ n ih => simp [terminal, ih]

theorem terminal_length (n : ℕ) : (terminal n).length = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [terminal, List.length_cons, ih]; omega

/-- Negative A/B are ruled out by an actually surviving inverse-rho token. -/
theorem positive_of_terminal_infix (e n : ℕ) (kind : Atom) (finish : List Token)
    (hi : expandAtom e kind <:+: finish) (he : values finish = terminal n) :
    kind = .a ∨ kind = .b := by
  have hn : ∀ t ∈ expandAtom e kind, t.value ≠ .rhoInv := by
    intro t hm hc
    apply terminal_no_inverse n
    rw [← he, values, ← hc]
    exact List.mem_map_of_mem (hi.sublist.subset hm)
  cases kind with
  | a => exact Or.inl rfl
  | b => exact Or.inr rfl
  | invA => exact False.elim (hn (leafToken e .rho .rhoInv) (by simp [expandAtom]) rfl)
  | invB => exact False.elim (hn (leafToken e .rho .rhoInv) (by simp [expandAtom]) rfl)

theorem terminal_pair_requires_positive_n (e n : ℕ) (kind : Atom) (finish : List Token)
    (hi : expandAtom e kind <:+: finish) (he : values finish = terminal n) : 1 ≤ n := by
  have hlen := hi.sublist.length_le
  have hl : finish.length = 2 * n + 1 := by
    have h := congrArg List.length he
    simpa [values, terminal_length] using h
  cases kind <;> simp only [expandAtom, List.length_cons, List.length_nil] at hlen <;> omega

/-- Terminal factors alone are not enough: original input, lawful trace and
whole-history untouchedness are explicit premises. -/
theorem recover_from_terminal (pre post : List (ℕ × Atom)) (e n : ℕ) (kind : Atom)
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace
      (expandChronological (pre ++ [(e,kind)] ++ post)) rules history finish)
    (hu : clean e history = true) (he : values finish = terminal n) :
    (kind = .a ∨ kind = .b) ∧ 1 ≤ n ∧
      ∃ p s, finish = p ++ expandAtom e kind ++ s := by
  have hi := original_pair_survives pre post e kind ht hu
  obtain ⟨p,s,hps⟩ := hi
  exact ⟨positive_of_terminal_infix e n kind finish ⟨p,s,hps⟩ he,
    terminal_pair_requires_positive_n e n kind finish ⟨p,s,hps⟩ he, p,s,hps.symm⟩

theorem numberFrom_append (k : ℕ) (pre post : List Atom) :
    numberFrom k (pre ++ post) =
      numberFrom k pre ++ numberFrom (k + pre.length) post := by
  induction pre generalizing k with
  | nil => simp [numberFrom]
  | cons kind pre ih =>
    simp only [List.cons_append, numberFrom, ih, List.length_cons]
    have he : k + 1 + pre.length = k + (pre.length + 1) := by omega
    rw [he]

theorem numbered_recovery (pre post : List Atom) (n : ℕ) (kind : Atom)
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace
      (expandChronological (numberFrom 0 (pre ++ kind :: post))) rules history finish)
    (hu : clean pre.length history = true) (he : values finish = terminal n) :
    (kind = .a ∨ kind = .b) ∧ 1 ≤ n ∧
      ∃ p s, finish = p ++ expandAtom pre.length kind ++ s := by
  have hinput : numberFrom 0 (pre ++ kind :: post) =
      numberFrom 0 pre ++ [(pre.length,kind)] ++ numberFrom (pre.length + 1) post := by
    simp [numberFrom_append, numberFrom]
  rw [hinput] at ht
  exact recover_from_terminal _ _ pre.length n kind ht hu he

/-- The live cut is bounded by the literal terminal length. No equality with
the original owner index is asserted. -/
theorem numbered_recovery_with_position (pre post : List Atom) (n : ℕ) (kind : Atom)
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace
      (expandChronological (numberFrom 0 (pre ++ kind :: post))) rules history finish)
    (hu : clean pre.length history = true) (he : values finish = terminal n) :
    (kind = .a ∨ kind = .b) ∧ 1 ≤ n ∧
      ∃ p s, finish = p ++ expandAtom pre.length kind ++ s ∧ p.length + 2 ≤ 2 * n + 1 := by
  obtain ⟨hk, hn, p, s, hps⟩ := numbered_recovery pre post n kind ht hu he
  refine ⟨hk, hn, p, s, hps, ?_⟩
  have hl : finish.length = 2 * n + 1 := by
    have h := congrArg List.length he
    simpa [values, terminal_length] using h
  have hpair : (expandAtom pre.length kind).length = 2 := by cases kind <;> rfl
  rw [hps, List.length_append, List.length_append, hpair] at hl
  omega

end Candidate.ShortWordRecovery

import ShortWordRecovery

/-! Syntactic terminal decrement after deletion of one wholly untouched,
canonically numbered original atom. No PSL/SL or original-run n-change claim. -/

namespace Candidate.ShortWordTerminalDelete
open ShortWordDelete ShortWordRecovery

def ownerTokens (e : ℕ) (w : List Token) : List Token :=
  w.filter (fun t => !(clean e t.support))

@[simp] theorem ownerTokens_nil (e : ℕ) : ownerTokens e [] = [] := rfl

@[simp] theorem ownerTokens_append (e : ℕ) (p s : List Token) :
    ownerTokens e (p ++ s) = ownerTokens e p ++ ownerTokens e s := by
  simp [ownerTokens]

theorem ownerTokens_output (e : ℕ) (r : Rule) (a b : Token)
    (ha : clean e a.support = true) (hb : clean e b.support = true) :
    ownerTokens e (output r a b) = [] := by
  cases r <;> simp [output, ownerTokens, ha, hb]

/-- Every token carrying e is literally unchanged, not merely counted. -/
theorem Trace.ownerTokens_preserved {start finish : List Token} {rules : List Rule}
    {history : List Leaf} (ht : ShortWordDelete.Trace start rules history finish)
    (e : ℕ) (hu : clean e history = true) :
    ownerTokens e finish = ownerTokens e start := by
  induction ht with
  | nil => rfl
  | step p s a b r legal tail ih =>
    simp only [clean_append, Bool.and_eq_true] at hu
    obtain ⟨⟨ha,hb⟩,hh⟩ := hu
    rw [ih hh]
    have hpair : ownerTokens e [a,b] = [] := by simp [ownerTokens, ha, hb]
    simp only [ownerTokens_append, ownerTokens_output e r a b ha hb, hpair,
      List.append_nil]

theorem ownerTokens_expandAtom (e k : ℕ) (kind : Atom) :
    ownerTokens e (expandAtom k kind) = if k = e then expandAtom k kind else [] := by
  cases kind <;> by_cases h : k = e <;>
    simp [ownerTokens, expandAtom, leafToken, clean, h]

theorem clean_leaves_iff (e : ℕ) (w : List Token) :
    clean e (leaves w) = true ↔ ∀ t ∈ w, clean e t.support = true := by
  induction w with
  | nil => simp [leaves]
  | cons t ts ih =>
    simp only [leaves] at ih
    simp [leaves, ih]

theorem ownerTokens_eq_nil_iff (e : ℕ) (w : List Token) :
    ownerTokens e w = [] ↔ clean e (leaves w) = true := by
  rw [clean_leaves_iff]
  simp [ownerTokens, List.filter_eq_nil_iff]

theorem numberFrom_owner_bounds (k : ℕ) (w : List Atom) (item : ℕ × Atom)
    (hm : item ∈ numberFrom k w) : k ≤ item.1 ∧ item.1 < k + w.length := by
  induction w generalizing k with
  | nil => simp [numberFrom] at hm
  | cons first rest ih =>
    simp only [numberFrom, List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp
    · obtain ⟨ha,hb⟩ := ih (k + 1) hm
      simp only [List.length_cons]
      omega

theorem ownerTokens_expand_none (e : ℕ) (atoms : List (ℕ × Atom))
    (h : ∀ item ∈ atoms, item.1 ≠ e) :
    ownerTokens e (expandChronological atoms) = [] := by
  induction atoms with
  | nil => rfl
  | cons item atoms ih =>
    have hhead := h item (by simp)
    have htail : ∀ a ∈ atoms, a.1 ≠ e := fun a ha => h a (by simp [ha])
    have he : expandChronological (item :: atoms) =
        expandChronological atoms ++ expandAtom item.1 item.2 := by
      simp [expandChronological]
    rw [he, ownerTokens_append, ih htail, ownerTokens_expandAtom, ite_eq_right hhead]
    rfl

theorem numbered_initial_ownerTokens (pre post : List Atom) (kind : Atom) :
    ownerTokens pre.length
      (expandChronological (numberFrom 0 (pre ++ kind :: post))) =
        expandAtom pre.length kind := by
  have hp : ownerTokens pre.length (expandChronological (numberFrom 0 pre)) = [] :=
    ownerTokens_expand_none _ _ (by
      intro item hm
      have h := (numberFrom_owner_bounds 0 pre item hm).2
      omega)
  have hs : ownerTokens pre.length
      (expandChronological (numberFrom (pre.length + 1) post)) = [] :=
    ownerTokens_expand_none _ _ (by
      intro item hm
      have h := (numberFrom_owner_bounds (pre.length + 1) post item hm).1
      omega)
  have hi : numberFrom 0 (pre ++ kind :: post) =
      numberFrom 0 pre ++ [(pre.length,kind)] ++ numberFrom (pre.length + 1) post := by
    simp [numberFrom_append, numberFrom]
  rw [hi]
  rw [expandChronological_append, expandChronological_append,
    ownerTokens_append, ownerTokens_append, hp, hs]
  have hsingle : expandChronological [(pre.length,kind)] = expandAtom pre.length kind := by
    simp [expandChronological]
  rw [hsingle, ownerTokens_expandAtom, ite_eq_left rfl]
  simp

/-- Outside the recovered pair, no final token contains even one e-leaf. -/
theorem clean_frame_of_projection (e : ℕ) (kind : Atom) (finish p s : List Token)
    (hframe : finish = p ++ expandAtom e kind ++ s)
    (hproj : ownerTokens e finish = expandAtom e kind) :
    clean e (leaves p ++ leaves s) = true := by
  rw [hframe, ownerTokens_append, ownerTokens_append, ownerTokens_expandAtom,
    ite_eq_left rfl] at hproj
  have hl := congrArg List.length hproj
  have hpair : (expandAtom e kind).length = 2 := by cases kind <;> rfl
  simp only [List.length_append, hpair] at hl
  have hp : ownerTokens e p = [] := List.length_eq_zero_iff.mp (by omega)
  have hs : ownerTokens e s = [] := List.length_eq_zero_iff.mp (by omega)
  simp only [clean_append, Bool.and_eq_true]
  exact ⟨(ownerTokens_eq_nil_iff e p).mp hp, (ownerTokens_eq_nil_iff e s).mp hs⟩

theorem numbered_final_clean_frame (pre post : List Atom) (kind : Atom)
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace
      (expandChronological (numberFrom 0 (pre ++ kind :: post))) rules history finish)
    (hu : clean pre.length history = true) :
    ∃ p s, finish = p ++ expandAtom pre.length kind ++ s ∧
      clean pre.length (leaves p ++ leaves s) = true := by
  have hinput : numberFrom 0 (pre ++ kind :: post) =
      numberFrom 0 pre ++ [(pre.length,kind)] ++ numberFrom (pre.length + 1) post := by
    simp [numberFrom_append, numberFrom]
  have hi := ht
  rw [hinput] at hi
  obtain ⟨p,s,hps⟩ := original_pair_survives _ _ pre.length kind hi hu
  have hframe := hps.symm
  have hproj := Trace.ownerTokens_preserved ht pre.length hu
  rw [numbered_initial_ownerTokens] at hproj
  exact ⟨p,s,hframe,clean_frame_of_projection pre.length kind finish p s hframe hproj⟩

theorem values_erase_clean (e : ℕ) (w : List Token)
    (hc : clean e (leaves w) = true) : values (eraseOwner e w) = values w := by
  have hf : w.filter (fun t => clean e t.support) = w := by
    apply List.filter_eq_self.mpr
    exact (clean_leaves_iff e w).mp hc
  simp only [eraseOwner, hf, values, List.map_map]
  rfl

/-- Exact alternating-list deletion, including a pair beginning at the rho
position. The zero case is impossible; n=1 decrements to terminal 0. -/
theorem terminal_delete_pair (n : ℕ) (p s : List Factor) (x y : Factor)
    (hk : (x = .sigma ∧ y = .rho) ∨ (x = .rho ∧ y = .sigma))
    (he : p ++ [x,y] ++ s = terminal n) : p ++ s = terminal (n - 1) := by
  induction n generalizing p s with
  | zero =>
    have hlen := congrArg List.length he
    simp [terminal] at hlen
    omega
  | succ n ih =>
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.nil_append, terminal,
        List.cons.injEq] at he
      simpa only [List.nil_append, Nat.add_sub_cancel] using he.2.2
    | cons c p =>
      simp only [List.cons_append, terminal, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      cases p with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.nil_append,
          List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        rcases hk with ⟨hbad,_⟩ | ⟨_,rfl⟩
        · contradiction
        · simpa only [List.cons_append, List.nil_append, Nat.add_sub_cancel] using he
      | cons d p =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        have hd := ih p s he
        cases n with
        | zero =>
          have hl := congrArg List.length he
          simp [terminal] at hl
          omega
        | succ m =>
          simpa only [List.cons_append, Nat.add_sub_cancel, terminal] using
            congrArg (fun w => Factor.sigma :: Factor.rho :: w) hd

theorem values_append (p s : List Token) : values (p ++ s) = values p ++ values s := by
  simp [values]

theorem erase_terminal_of_clean_frame (e n : ℕ) (kind : Atom) (finish p s : List Token)
    (hk : kind = .a ∨ kind = .b) (hframe : finish = p ++ expandAtom e kind ++ s)
    (hc : clean e (leaves p ++ leaves s) = true) (he : values finish = terminal n) :
    values (eraseOwner e finish) = terminal (n - 1) := by
  have hh : clean e (leaves p) = true ∧ clean e (leaves s) = true := by
    simpa only [clean_append, Bool.and_eq_true] using hc
  obtain ⟨hcp,hcs⟩ := hh
  rw [hframe, eraseOwner_append, eraseOwner_append, eraseOwner_expandAtom,
    ite_eq_left rfl, List.append_nil]
  change values (eraseOwner e p ++ eraseOwner e s) = _
  rw [values_append, values_erase_clean e p hcp, values_erase_clean e s hcs]
  rw [hframe] at he
  simp only [values_append] at he
  rcases hk with rfl | rfl
  · exact terminal_delete_pair n _ _ .sigma .rho (Or.inl ⟨rfl,rfl⟩)
      (by simpa [values, expandAtom, leafToken] using he)
  · exact terminal_delete_pair n _ _ .rho .sigma (Or.inr ⟨rfl,rfl⟩)
      (by simpa [values, expandAtom, leafToken] using he)

/-- Combines the independently stated local components. No edited trace or
edited terminal equality appears among the assumptions. -/
theorem numbered_terminal_deletion (pre post : List Atom) (n : ℕ) (kind : Atom)
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace
      (expandChronological (numberFrom 0 (pre ++ kind :: post))) rules history finish)
    (hu : clean pre.length history = true) (he : values finish = terminal n) :
    ShortWordDelete.Trace (expandChronological (numberFrom 0 (pre ++ post))) rules
      (history.map (relabelLeaf pre.length)) (eraseOwner pre.length finish) ∧
      values (eraseOwner pre.length finish) = terminal (n - 1) := by
  obtain ⟨hk,_,_⟩ := numbered_recovery pre post n kind ht hu he
  obtain ⟨p,s,hframe,hclean⟩ := numbered_final_clean_frame pre post kind ht hu
  exact ⟨numbered_deletion_replay pre post kind ht hu,
    erase_terminal_of_clean_frame pre.length n kind finish p s hk hframe hclean he⟩

theorem numbered_terminal_deletion_research (pre post : List Atom) (n : ℕ) (kind : Atom)
    {rules : List Rule} {history : List Leaf} {finish : List Token} (hn : 7 ≤ n)
    (ht : ShortWordDelete.Trace
      (expandChronological (numberFrom 0 (pre ++ kind :: post))) rules history finish)
    (hu : clean pre.length history = true) (he : values finish = terminal n) :
    6 ≤ n - 1 ∧ ShortWordDelete.Trace
      (expandChronological (numberFrom 0 (pre ++ post))) rules
      (history.map (relabelLeaf pre.length)) (eraseOwner pre.length finish) ∧
      values (eraseOwner pre.length finish) = terminal (n - 1) := by
  exact ⟨by omega, numbered_terminal_deletion pre post n kind ht hu he⟩

end Candidate.ShortWordTerminalDelete

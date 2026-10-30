import ShortWordLineage
namespace Candidate.ShortWordAdjacency
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordTerminalDelete
open Candidate.ShortWordLineage

def Neighbors (c x : Token) (w : List Token) : Prop := [c,x] <:+: w ∨ [x,c] <:+: w

theorem right_at_cut {α : Type} {c x : α} {p s : List α}
    (hp : c ∉ p) (hs : c ∉ s) (h : [c,x] <:+: p ++ c :: s) :
    ∃ rest, s = x :: rest := by
  induction p with
  | nil =>
    rcases List.infix_cons_iff.mp h with h | h
    · exact ((pair_prefix_iff c x c s).mp h).2
    · exact False.elim (hs (h.subset (by simp)))
  | cons d p ih =>
    simp only [List.mem_cons, not_or] at hp
    rcases List.infix_cons_iff.mp h with h | h
    · exact False.elim (hp.1 ((pair_prefix_iff c x d _).mp h).1)
    · exact ih hp.2 h

theorem left_at_cut {α : Type} {c x : α} {p s : List α}
    (hp : c ∉ p) (hs : c ∉ s) (hxc : x ≠ c) (h : [x,c] <:+: p ++ c :: s) :
    ∃ pre, p = pre ++ [x] := by
  induction p with
  | nil =>
    rcases List.infix_cons_iff.mp h with h | h
    · exact False.elim (hxc ((pair_prefix_iff x c c s).mp h).1)
    · exact False.elim (hs (h.subset (by simp)))
  | cons d p ih =>
    simp only [List.mem_cons, not_or] at hp
    rcases List.infix_cons_iff.mp h with h | h
    · obtain ⟨rfl, rest, he⟩ := (pair_prefix_iff x c d _).mp h
      cases p with
      | nil => exact ⟨[], rfl⟩
      | cons z p =>
        have hz := (List.cons.inj he).1
        exact False.elim (hp.2 (by simp [hz]))
    · obtain ⟨pre, he⟩ := ih hp.2 h
      exact ⟨d :: pre, by simp [he]⟩

theorem token_not_frame (p s : List Token) (c : Token)
    (hd : (leaves (p ++ c :: s)).Nodup) (hne : c.support ≠ []) : c ∉ p ∧ c ∉ s := by
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hne
  have h : leaves (p ++ c :: s) = leaves p ++ c.support ++ leaves s := by
    simp [leaves, List.append_assoc]
  rw [h] at hd
  constructor
  · intro hc
    have hm : l ∈ leaves p := List.mem_flatMap.mpr ⟨c,hc,hl⟩
    exact (List.nodup_append.mp (List.nodup_append.mp hd).1).2.2 l hm l hl rfl
  · intro hc
    have hm : l ∈ leaves s := List.mem_flatMap.mpr ⟨c,hc,hl⟩
    exact (List.nodup_append.mp hd).2.2 l (List.mem_append_right _ hl) l hm rfl

/-- Pure list locality, with an arbitrary protected-token predicate. -/
theorem protected_pair_step (f : Token → Bool) (x y a b : Token)
    (hx : f x = false) (hy : f y = false) (ha : f a = true) (hb : f b = true)
    (p s replacement : List Token) (hin : [x,y] <:+: p ++ [a,b] ++ s) :
    [x,y] <:+: p ++ replacement ++ s := by
  induction p with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.nil_append] at hin ⊢
    rcases List.infix_cons_iff.mp hin with hp | hin
    · have he := (pair_prefix_iff x y a _).mp hp
      have := congrArg f he.1
      rw [hx, ha] at this
      contradiction
    · rcases List.infix_cons_iff.mp hin with hp | hin
      · have he := (pair_prefix_iff x y b _).mp hp
        have := congrArg f he.1
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
        have := congrArg f hay
        rw [ha, hy] at this
        contradiction
      | cons d p =>
        simp only [List.cons_append] at he
        have hdy : d = y := (List.cons.inj he).1
        subst d
        exact ⟨[], p ++ replacement ++ s, rfl⟩
    · exact List.infix_cons (ih hin)

theorem protected_pair_ne (x y a b : Token) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (p s replacement : List Token)
    (hin : [x,y] <:+: p ++ [a,b] ++ s) : [x,y] <:+: p ++ replacement ++ s := by
  exact protected_pair_step (fun t => decide (t ≠ x ∧ t ≠ y)) x y a b
    (by simp) (by simp) (by simp [hax,hay]) (by simp [hbx,hby]) p s replacement hin

theorem terminal_no_rho_pair (n : ℕ) (x y : Factor)
    (hx : x ≠ .sigma) (hy : y ≠ .sigma) : ¬ [x,y] <:+: terminal n := by
  induction n with
  | zero =>
    intro h
    have := h.length_le
    simp [terminal] at this
  | succ n ih =>
    intro h
    rcases List.infix_cons_iff.mp h with h | h
    · exact hx ((pair_prefix_iff x y .sigma _).mp h).1
    · rcases List.infix_cons_iff.mp h with h | h
      · obtain ⟨_, s, he⟩ := (pair_prefix_iff x y .rho _).mp h
        cases n <;> simp only [terminal, List.cons.injEq] at he <;> exact hy he.1.symm
      · exact ih h

theorem terminal_no_neighbors {finish : List Token} {n : ℕ} (he : values finish = terminal n)
    {x y : Token} (hx : x.value ≠ .sigma) (hy : y.value ≠ .sigma) :
    ¬ Neighbors x y finish := by
  rintro (h | h)
  · have hm := h.map Token.value
    change values _ <:+: values finish at hm
    rw [he] at hm
    exact terminal_no_rho_pair n x.value y.value hx hy hm
  · have hm := h.map Token.value
    change values _ <:+: values finish at hm
    rw [he] at hm
    exact terminal_no_rho_pair n y.value x.value hy hx hm
end Candidate.ShortWordAdjacency

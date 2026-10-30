import ShortWordOverlap
namespace Candidate.ShortWordNoZ
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordTerminalDelete
open Candidate.ShortWordLineage Candidate.ShortWordAdjacency Candidate.ShortWordOverlap
open Candidate.ShortWordMarkAccounting

theorem neighbor_merge {p s : List Token} {a b c x m : Token} {l : Leaf}
    (hd : (leaves (p ++ [a,b] ++ s)).Nodup) (ha : a.support ≠ []) (hb : b.support ≠ [])
    (hca : c ≠ a) (hcb : c ≠ b) (hx : Neighbors c x (p ++ [a,b] ++ s))
    (hxl : l ∈ x.support) (hxv : x.value ≠ .sigma)
    (hmv : m.value ≠ .sigma) (hm : m.support = a.support ++ b.support) :
    ∃ y, y.value ≠ .sigma ∧ l ∈ y.support ∧ Neighbors c y (p ++ [m] ++ s) := by
  have cuta := token_not_frame p (b :: s) a (by simpa [List.append_assoc] using hd) ha
  have cutb := token_not_frame (p ++ [a]) s b (by simpa [List.append_assoc] using hd) hb
  by_cases hxa : x = a
  · subst x
    rcases hx with hx | hx
    · obtain ⟨pre,hp⟩ := left_at_cut cuta.1 cuta.2 hca (by simpa [List.append_assoc] using hx)
      refine ⟨m,hmv,by rw [hm]; exact List.mem_append_left _ hxl,Or.inl ?_⟩
      exact ⟨pre,s,by simp [hp,List.append_assoc]⟩
    · obtain ⟨rest,he⟩ := right_at_cut cuta.1 cuta.2 (by simpa [List.append_assoc] using hx)
      exact False.elim (hcb (List.cons.inj he).1.symm)
  · by_cases hxb : x = b
    · subst x
      rcases hx with hx | hx
      · obtain ⟨pre,hp⟩ := left_at_cut cutb.1 cutb.2 hcb (by simpa [List.append_assoc] using hx)
        have hh := congrArg List.getLast? hp
        simp only [List.getLast?_append, List.getLast?_singleton] at hh
        exact False.elim (hca (Option.some.inj hh).symm)
      · obtain ⟨rest,hs⟩ := right_at_cut cutb.1 cutb.2 (by simpa [List.append_assoc] using hx)
        refine ⟨m,hmv,by rw [hm]; exact List.mem_append_right _ hxl,Or.inr ?_⟩
        exact ⟨p,rest,by simp [hs,List.append_assoc]⟩
    · refine ⟨x,hxv,hxl,?_⟩
      rcases hx with hx | hx
      · exact Or.inl (protected_pair_ne c x a b hca.symm (Ne.symm hxa) hcb.symm (Ne.symm hxb) p s [m] hx)
      · exact Or.inr (protected_pair_ne x c a b (Ne.symm hxa) hca.symm (Ne.symm hxb) hcb.symm p s [m] hx)

theorem neighbor_step_no_z {p s : List Token} {a b c x : Token} {l : Leaf} {r : Rule}
    (hl : Legal r a b) (hz : r ≠ .z) (hd : (leaves (p ++ [a,b] ++ s)).Nodup)
    (hca : c ≠ a) (hcb : c ≠ b) (hx : Neighbors c x (p ++ [a,b] ++ s))
    (hxl : l ∈ x.support) (hxv : x.value ≠ .sigma) :
    ∃ y, y.value ≠ .sigma ∧ l ∈ y.support ∧ Neighbors c y (p ++ output r a b ++ s) := by
  cases r with
  | t =>
    have hxa : x ≠ a := fun he => hxv (he ▸ hl.2.2.1)
    have hxb : x ≠ b := fun he => hxv (he ▸ hl.2.2.2)
    refine ⟨x,hxv,hxl,?_⟩
    rcases hx with hx | hx
    · exact Or.inl (protected_pair_ne c x a b hca.symm (Ne.symm hxa) hcb.symm (Ne.symm hxb) p s [] hx)
    · exact Or.inr (protected_pair_ne x c a b (Ne.symm hxa) hca.symm (Ne.symm hxb) hcb.symm p s [] hx)
  | u => exact neighbor_merge hd hl.1 hl.2.1 hca hcb hx hxl hxv (by simp) rfl
  | v => exact neighbor_merge hd hl.1 hl.2.1 hca hcb hx hxl hxv (by simp) rfl
  | z => exact False.elim (hz rfl)

theorem companions_step_no_z {p s : List Token} {a b : Token} {r : Rule}
    (hl : Legal r a b) (hz : r ≠ .z) (hw : TypedState (p ++ [a,b] ++ s))
    (hd : (leaves (p ++ [a,b] ++ s)).Nodup) (hc : Companions ∅ (p ++ [a,b] ++ s)) :
    Companions ∅ (p ++ output r a b ++ s) := by
  intro e _ hm
  let c := leafToken e .sigma .sigma
  have hlive : (Leaf.mk e .sigma) ∈ leaves (p ++ output r a b ++ s) :=
    List.mem_flatMap.mpr ⟨c, hm, by simp [c,leafToken]⟩
  have hnot := fun h => sigma_input_absent_output hl hw hd ⟨e,.sigma⟩ rfl h hlive
  have hca : c ≠ a := by intro eq; apply hnot; simp [← eq,c,leafToken]
  have hcb : c ≠ b := by intro eq; apply hnot; simp [← eq,c,leafToken]
  have hcm : c ∈ p ++ [a,b] ++ s := by
    simp only [List.mem_append] at hm
    rcases hm with (hp | ho) | hs
    · simp [hp,c]
    · cases r <;> simp [output,leafToken] at ho
    · simp [hs,c]
  obtain ⟨x,hxv,hxl,hx⟩ := hc e (by simp) hcm
  exact neighbor_step_no_z hl hz hd hca hcb hx hxl hxv

/-- With no rho annihilation, a rho neighbor of a protected rho cannot disappear.
This holds for arbitrary legal rewrite order, including outward mergers. -/
theorem rho_neighbor_must_mark {start finish : List Token} {rules : List Rule} {history : List Leaf}
    (ht : ShortWordDelete.Trace start rules history finish) (hz : Rule.z ∉ rules)
    (hd : (leaves start).Nodup) {n e : ℕ} (heq : values finish = terminal n)
    {c x : Token} (hcv : c.value ≠ .sigma) (hxv : x.value ≠ .sigma)
    (hcl : (Leaf.mk e .rho) ∈ c.support) (hxne : x.support ≠ [])
    (hx : Neighbors c x start) : e ∈ marks .rho history := by
  by_contra he
  induction ht generalizing x with
  | nil w => exact terminal_no_neighbors heq hcv hxv hx
  | @step p s a b r rs h w hl tail ih =>
    simp only [marks_append, Finset.mem_union, not_or] at he
    have hca : c ≠ a := by
      intro eq; subst c
      exact he.1.1 ((mem_marks_iff e .rho a.support).mpr ⟨⟨e,.rho⟩,hcl,rfl,rfl⟩)
    have hcb : c ≠ b := by
      intro eq; subst c
      exact he.1.2 ((mem_marks_iff e .rho b.support).mpr ⟨⟨e,.rho⟩,hcl,rfl,rfl⟩)
    have hz' : r ≠ .z ∧ Rule.z ∉ rs := by simpa [eq_comm] using hz
    obtain ⟨l,hlx⟩ := List.exists_mem_of_ne_nil _ hxne
    obtain ⟨y,hyv,hyl,hy⟩ := neighbor_step_no_z hl hz'.1 hd hca hcb hx hlx hxv
    exact ih hz'.2 (hd.sublist (leaves_step_sublist p s a b r)) heq hyv
      (List.ne_nil_of_mem hyl) hy he.2

theorem t_both_marked_no_z {p s : List Token} {e f n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (hd : (leaves (p ++ [leafToken e .sigma .sigma, leafToken f .sigma .sigma] ++ s)).Nodup)
    (hc : Companions ∅ (p ++ [leafToken e .sigma .sigma, leafToken f .sigma .sigma] ++ s))
    (ht : ShortWordDelete.Trace (p ++ s) rules history finish) (hz : Rule.z ∉ rules)
    (heq : values finish = terminal n) : e ∈ marks .rho history ∧ f ∈ marks .rho history := by
  obtain ⟨p',s',x,y,hp,hs,hxv,hyv,hxl,hyl⟩ := exterior_companions hd
    (hc e (by simp) (by simp)) (hc f (by simp) (by simp))
  have hin : [x,y] <:+: p ++ s := ⟨p',s',by simp [hp,hs,List.append_assoc]⟩
  have hd' : (leaves (p ++ s)).Nodup := by
    exact hd.sublist (by simpa [output] using
      leaves_step_sublist p s (leafToken e .sigma .sigma) (leafToken f .sigma .sigma) .t)
  exact ⟨rho_neighbor_must_mark ht hz hd' heq hxv hyv hxl (List.ne_nil_of_mem hyl) (Or.inl hin),
    rho_neighbor_must_mark ht hz hd' heq hyv hxv hyl (List.ne_nil_of_mem hxl) (Or.inr hin)⟩

theorem sigma_subset_rho_no_z {start finish : List Token} {rules : List Rule} {history : List Leaf}
    (ht : ShortWordDelete.Trace start rules history finish) (hz : Rule.z ∉ rules) {n : ℕ}
    (heq : values finish = terminal n) (hw : TypedState start) (hd : (leaves start).Nodup)
    (hs : SigmaSingleton start) (hc : Companions ∅ start) :
    marks .sigma history ⊆ marks .rho history := by
  induction ht with
  | nil => simp [marks]
  | @step p s a b r rs h w hl tail ih =>
    have hz' : r ≠ .z ∧ Rule.z ∉ rs := by simpa [eq_comm] using hz
    have hi := ih hz'.2 heq (typed_step hl hw) (hd.sublist (leaves_step_sublist p s a b r))
      (sigma_singleton_step r hs) (companions_step_no_z hl hz'.1 hw hd hc)
    cases r with
    | t =>
      obtain ⟨e,rfl⟩ := hs a (by simp) hl.2.2.1
      obtain ⟨f,rfl⟩ := hs b (by simp) hl.2.2.2
      have hm := t_both_marked_no_z hd hc (by simpa [output] using tail) hz'.2 heq
      simp only [marks_append]
      intro k hk
      simp [marks,leafToken] at hk ⊢
      rcases hk with rfl | rfl | hk
      · simpa [marks] using hm.1
      · simpa [marks] using hm.2
      · simpa [marks] using hi (by simpa [marks] using hk)
    | u =>
      have ea := sigma_marks_empty_of_rho a (hw a (by simp)) (by simp [hl.2.2.1])
      have eb := sigma_marks_empty_of_rho b (hw b (by simp)) (by simp [hl.2.2.2])
      rw [marks_append, marks_append, ea, eb, Finset.empty_union, Finset.empty_union]
      exact hi.trans (by intro k hk; simp only [marks_append, Finset.mem_union]; exact Or.inr hk)
    | v =>
      have ea := sigma_marks_empty_of_rho a (hw a (by simp)) (by simp [hl.2.2.1])
      have eb := sigma_marks_empty_of_rho b (hw b (by simp)) (by simp [hl.2.2.2])
      rw [marks_append, marks_append, ea, eb, Finset.empty_union, Finset.empty_union]
      exact hi.trans (by intro k hk; simp only [marks_append, Finset.mem_union]; exact Or.inr hk)
    | z => exact False.elim (hz'.1 rfl)

end Candidate.ShortWordNoZ

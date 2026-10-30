import ShortWordAdjacency
namespace Candidate.ShortWordOverlap
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordTerminalDelete
open Candidate.ShortWordSelection Candidate.ShortWordCounts Candidate.ShortWordMarkAccounting
open Candidate.ShortWordLineage Candidate.ShortWordAdjacency

def HasCompanion (e : ℕ) (w : List Token) : Prop :=
  ∃ x : Token, x.value ≠ .sigma ∧ (Leaf.mk e .rho) ∈ x.support ∧
    Neighbors (leafToken e .sigma .sigma) x w

def Companions (R : Finset ℕ) (w : List Token) : Prop :=
  ∀ e, e ∉ R → leafToken e .sigma .sigma ∈ w → HasCompanion e w

theorem initial_companions (atoms : List Atom) (R : Finset ℕ) :
    Companions R (expandChronological (numberFrom 0 atoms)) := by
  intro e _ hm
  have hl : (Leaf.mk e .sigma) ∈ leaves (expandChronological (numberFrom 0 atoms)) :=
    List.mem_flatMap.mpr ⟨leafToken e .sigma .sigma, hm, by simp [leafToken]⟩
  have hb := (initial_leaf_owner 0 atoms ⟨e,.sigma⟩ hl).2
  obtain ⟨pre, kind, post, hs, hp⟩ := split_at_position atoms e (by simpa using hb)
  have hnum : numberFrom 0 atoms =
      numberFrom 0 pre ++ [(e,kind)] ++ numberFrom (e+1) post := by
    simp [hs, numberFrom_append, numberFrom, hp]
  have hi := original_block_infix (numberFrom 0 pre) (numberFrom (e+1) post) e kind
  rw [← hnum] at hi
  cases kind with
  | a => exact ⟨leafToken e .rho .rho, by simp [leafToken], by simp [leafToken], Or.inl hi⟩
  | invA => exact ⟨leafToken e .rho .rhoInv, by simp [leafToken], by simp [leafToken], Or.inr hi⟩
  | invB => exact ⟨leafToken e .rho .rhoInv, by simp [leafToken], by simp [leafToken], Or.inl hi⟩
  | b => exact ⟨leafToken e .rho .rho, by simp [leafToken], by simp [leafToken], Or.inr hi⟩

theorem outside_rho_ne {R : Finset ℕ} {a x : Token} {e : ℕ}
    (ha : marks .rho a.support ⊆ R) (he : e ∉ R) (hx : (Leaf.mk e .rho) ∈ x.support) : a ≠ x := by
  intro eq
  subst x
  exact he (ha ((mem_marks_iff e .rho a.support).mpr ⟨⟨e,.rho⟩, hx, rfl, rfl⟩))

theorem companions_step {R : Finset ℕ} {p s : List Token} {a b : Token} {r : Rule}
    (hl : Legal r a b) (hw : TypedState (p ++ [a,b] ++ s))
    (hd : (leaves (p ++ [a,b] ++ s)).Nodup)
    (hc : Companions R (p ++ [a,b] ++ s))
    (haR : marks .rho a.support ⊆ R) (hbR : marks .rho b.support ⊆ R) :
    Companions R (p ++ output r a b ++ s) := by
  intro e he hm
  let c := leafToken e .sigma .sigma
  have hlive : (Leaf.mk e .sigma) ∈ leaves (p ++ output r a b ++ s) :=
    List.mem_flatMap.mpr ⟨c, hm, by simp [c, leafToken]⟩
  have hnot := fun h => sigma_input_absent_output hl hw hd ⟨e,.sigma⟩ rfl h hlive
  have hac : a ≠ c := by
    intro eq; apply hnot; simp [eq, c, leafToken]
  have hbc : b ≠ c := by
    intro eq; apply hnot; simp [eq, c, leafToken]
  have hcm : c ∈ p ++ [a,b] ++ s := by
    simp only [List.mem_append] at hm
    rcases hm with (hp | ho) | hs
    · simp [hp, c]
    · cases r <;> simp [output, leafToken] at ho
    · simp [hs, c]
  obtain ⟨x, hxv, hxl, hx⟩ := hc e he hcm
  have hax := outside_rho_ne haR he hxl
  have hbx := outside_rho_ne hbR he hxl
  refine ⟨x,hxv,hxl,?_⟩
  rcases hx with hx | hx
  · exact Or.inl (protected_pair_ne c x a b hac hax hbc hbx p s _ hx)
  · exact Or.inr (protected_pair_ne x c a b hax hac hbx hbc p s _ hx)

theorem Trace.protected_rho_pair {start finish : List Token} {rules : List Rule} {history : List Leaf}
    (ht : ShortWordDelete.Trace start rules history finish) {R : Finset ℕ}
    (hR : marks .rho history ⊆ R) {e f : ℕ} (he : e ∉ R) (hf : f ∉ R)
    {x y : Token} (hx : (Leaf.mk e .rho) ∈ x.support) (hy : (Leaf.mk f .rho) ∈ y.support)
    (hi : [x,y] <:+: start) : [x,y] <:+: finish := by
  induction ht with
  | nil => exact hi
  | step p s a b r hl tail ih =>
    simp only [marks_append, Finset.union_subset_iff] at hR
    exact ih hR.2 (protected_pair_ne x y a b
      (outside_rho_ne hR.1.1 he hx) (outside_rho_ne hR.1.1 hf hy)
      (outside_rho_ne hR.1.2 he hx) (outside_rho_ne hR.1.2 hf hy) p s _ hi)

/-- Two adjacent singleton sigmas with companions have exterior rho neighbors. -/
theorem exterior_companions {p s : List Token} {e f : ℕ}
    (hd : (leaves (p ++ [leafToken e .sigma .sigma, leafToken f .sigma .sigma] ++ s)).Nodup)
    (he : HasCompanion e (p ++ [leafToken e .sigma .sigma, leafToken f .sigma .sigma] ++ s))
    (hf : HasCompanion f (p ++ [leafToken e .sigma .sigma, leafToken f .sigma .sigma] ++ s)) :
    ∃ p' s' x y, p = p' ++ [x] ∧ s = y :: s' ∧
      x.value ≠ .sigma ∧ y.value ≠ .sigma ∧
      (Leaf.mk e .rho) ∈ x.support ∧ (Leaf.mk f .rho) ∈ y.support := by
  let a := leafToken e .sigma .sigma
  let b := leafToken f .sigma .sigma
  have hda : (leaves (p ++ a :: (b :: s))).Nodup := by simpa [a,b,List.append_assoc] using hd
  have hdb : (leaves ((p ++ [a]) ++ b :: s)).Nodup := by simpa [a,b,List.append_assoc] using hd
  have ha := token_not_frame p (b :: s) a hda (by simp [a,leafToken])
  have hb := token_not_frame (p ++ [a]) s b hdb (by simp [b,leafToken])
  obtain ⟨x, hxv, hxl, hx⟩ := he
  obtain ⟨y, hyv, hyl, hy⟩ := hf
  have hxa : x ≠ a := fun h => hxv (by rw [h]; rfl)
  have hyb : y ≠ b := fun h => hyv (by rw [h]; rfl)
  have hp : ∃ p', p = p' ++ [x] := by
    rcases hx with hx | hx
    · obtain ⟨rest, heq⟩ := right_at_cut ha.1 ha.2 (by simpa [a,b,List.append_assoc] using hx)
      have hbx := (List.cons.inj heq).1
      exact False.elim (hxv (by rw [← hbx]; rfl))
    · exact left_at_cut ha.1 ha.2 hxa (by simpa [a,b,List.append_assoc] using hx)
  have hs : ∃ s', s = y :: s' := by
    rcases hy with hy | hy
    · exact right_at_cut hb.1 hb.2 (by simpa [a,b,List.append_assoc] using hy)
    · obtain ⟨pre, heq⟩ := left_at_cut hb.1 hb.2 hyb (by simpa [a,b,List.append_assoc] using hy)
      have hlast := congrArg List.getLast? heq
      simp only [List.getLast?_append, List.getLast?_singleton] at hlast
      have hay : a = y := Option.some.inj hlast
      exact False.elim (hyv (by rw [← hay]; rfl))
  obtain ⟨p',hp⟩ := hp
  obtain ⟨s',hs⟩ := hs
  exact ⟨p',s',x,y,hp,hs,hxv,hyv,hxl,hyl⟩

theorem t_overlap {R : Finset ℕ} {p s : List Token} {e f n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (hd : (leaves (p ++ [leafToken e .sigma .sigma, leafToken f .sigma .sigma] ++ s)).Nodup)
    (hc : Companions R (p ++ [leafToken e .sigma .sigma, leafToken f .sigma .sigma] ++ s))
    (ht : ShortWordDelete.Trace (p ++ s) rules history finish)
    (hh : marks .rho history ⊆ R) (heq : values finish = terminal n) : e ∈ R ∨ f ∈ R := by
  by_contra h
  simp only [not_or] at h
  obtain ⟨p',s',x,y,hp,hs,hxv,hyv,hxl,hyl⟩ := exterior_companions hd
    (hc e h.1 (by simp)) (hc f h.2 (by simp))
  have hin : [x,y] <:+: p ++ s := ⟨p',s',by simp [hp,hs,List.append_assoc]⟩
  have hout := Trace.protected_rho_pair ht hh h.1 h.2 hxl hyl hin
  exact terminal_no_neighbors heq hxv hyv (Or.inl hout)

theorem sigma_marks_empty_of_rho (t : Token) (ht : TypedToken t) (hv : t.value ≠ .sigma) :
    marks .sigma t.support = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e hm
  obtain ⟨l, hl, _, htag⟩ := (mem_marks_iff e .sigma t.support).mp hm
  have hh := ht.2 l hl
  cases he : t.value <;> simp [he, factorTag, htag] at hh hv

theorem sigma_outside_bound {start finish : List Token} {rules : List Rule} {history : List Leaf}
    (ht : ShortWordDelete.Trace start rules history finish) {R : Finset ℕ} {n : ℕ}
    (hh : marks .rho history ⊆ R) (heq : values finish = terminal n)
    (hw : TypedState start) (hd : (leaves start).Nodup) (hs : SigmaSingleton start)
    (hc : Companions R start) : (marks .sigma history \ R).card ≤ rules.count .t := by
  induction ht with
  | nil => simp [marks]
  | @step p s a b r rs h w hl tail ih =>
    have hh' := hh
    simp only [marks_append, Finset.union_subset_iff] at hh'
    have htail := ih hh'.2 heq (typed_step hl hw)
      (hd.sublist (leaves_step_sublist p s a b r)) (sigma_singleton_step r hs)
      (companions_step hl hw hd hc hh'.1.1 hh'.1.2)
    have hcard := Finset.card_union_le
      ((marks .sigma a.support ∪ marks .sigma b.support) \ R)
      (marks .sigma h \ R)
    rw [← Finset.union_sdiff_distrib] at hcard
    simp only [marks_append] at *
    cases r with
    | t =>
      obtain ⟨e, rfl⟩ := hs a (by simp) hl.2.2.1
      obtain ⟨f, rfl⟩ := hs b (by simp) hl.2.2.2
      have hov := t_overlap hd hc (by simpa [output] using tail) hh'.2 heq
      have hsmall : ((marks .sigma (leafToken e .sigma .sigma).support ∪
          marks .sigma (leafToken f .sigma .sigma).support) \ R).card ≤ 1 := by
        rcases hov with he | hf
        · have hsub : ((marks .sigma (leafToken e .sigma .sigma).support ∪
                marks .sigma (leafToken f .sigma .sigma).support) \ R) ⊆ {f} := by
            intro x hx
            simp [leafToken,marks] at hx ⊢
            aesop
          simpa using Finset.card_le_card hsub
        · have hsub : ((marks .sigma (leafToken e .sigma .sigma).support ∪
                marks .sigma (leafToken f .sigma .sigma).support) \ R) ⊆ {e} := by
            intro x hx
            simp [leafToken,marks] at hx ⊢
            aesop
          simpa using Finset.card_le_card hsub
      simp only [List.count_cons_self] at ⊢
      omega
    | u =>
      have ea := sigma_marks_empty_of_rho a (hw a (by simp)) (by simp [hl.2.2.1])
      have eb := sigma_marks_empty_of_rho b (hw b (by simp)) (by simp [hl.2.2.2])
      simpa [ea,eb] using htail
    | v =>
      have ea := sigma_marks_empty_of_rho a (hw a (by simp)) (by simp [hl.2.2.1])
      have eb := sigma_marks_empty_of_rho b (hw b (by simp)) (by simp [hl.2.2.2])
      simpa [ea,eb] using htail
    | z =>
      have hva : a.value ≠ .sigma := by rcases hl.2.2 with h | h <;> simp [h.1]
      have hvb : b.value ≠ .sigma := by rcases hl.2.2 with h | h <;> simp [h.2]
      have ea := sigma_marks_empty_of_rho a (hw a (by simp)) hva
      have eb := sigma_marks_empty_of_rho b (hw b (by simp)) hvb
      simpa [ea,eb] using htail

end Candidate.ShortWordOverlap

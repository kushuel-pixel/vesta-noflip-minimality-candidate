import Verify.AtomicSemantics

/-! Local original-leaf trace semantics and replay after deleting one untouched
owner. No PSL/B3 interpretation, endpoint-normal-form theorem or global cover. -/

namespace Candidate.ShortWordDelete

inductive Tag where | sigma | rho deriving DecidableEq, Repr
inductive Factor where | sigma | rho | rhoInv deriving DecidableEq, Repr
inductive Atom where | a | invA | invB | b deriving DecidableEq, Repr
inductive Rule where | t | u | v | z deriving DecidableEq, Repr

structure Leaf where
  owner : ℕ
  tag : Tag
  deriving DecidableEq, Repr

structure Token where
  value : Factor
  support : List Leaf
  deriving DecidableEq, Repr

def clean (e : ℕ) (ls : List Leaf) : Bool :=
  ls.all (fun l => l.owner != e)

def Legal (r : Rule) (a b : Token) : Prop :=
  a.support ≠ [] ∧ b.support ≠ [] ∧
  match r with
  | .t => a.value = .sigma ∧ b.value = .sigma
  | .u => a.value = .rhoInv ∧ b.value = .rhoInv
  | .v => a.value = .rho ∧ b.value = .rho
  | .z => (a.value = .rho ∧ b.value = .rhoInv) ∨
      (a.value = .rhoInv ∧ b.value = .rho)

def output (r : Rule) (a b : Token) : List Token :=
  match r with
  | .t | .z => []
  | .u => [⟨.rho, a.support ++ b.support⟩]
  | .v => [⟨.rhoInv, a.support ++ b.support⟩]

/-- The history records *all* inputs, including those later annihilated.
Positions are the actual current prefix length, not original word indices. -/
inductive Trace : List Token → List Rule → List Leaf → List Token → Prop where
  | nil (w) : Trace w [] [] w
  | step (p s : List Token) (a b : Token) (r : Rule)
      {rs : List Rule} {h : List Leaf} {w : List Token}
      (legal : Legal r a b)
      (tail : Trace (p ++ output r a b ++ s) rs h w) :
      Trace (p ++ [a,b] ++ s) (r :: rs) (a.support ++ b.support ++ h) w

def renameOwner (e k : ℕ) : ℕ := if k < e then k else k - 1

def relabelLeaf (e : ℕ) (l : Leaf) : Leaf :=
  ⟨renameOwner e l.owner, l.tag⟩

def relabelToken (e : ℕ) (t : Token) : Token :=
  ⟨t.value, t.support.map (relabelLeaf e)⟩

def eraseOwner (e : ℕ) (w : List Token) : List Token :=
  (w.filter (fun t => clean e t.support)).map (relabelToken e)

def leafToken (k : ℕ) (tag : Tag) (value : Factor) : Token :=
  ⟨value, [⟨k, tag⟩]⟩

def expandAtom (k : ℕ) : Atom → List Token
  | .a => [leafToken k .sigma .sigma, leafToken k .rho .rho]
  | .invA => [leafToken k .rho .rhoInv, leafToken k .sigma .sigma]
  | .invB => [leafToken k .sigma .sigma, leafToken k .rho .rhoInv]
  | .b => [leafToken k .rho .rho, leafToken k .sigma .sigma]

/-- Input is chronological owned Nielsen atoms. Reverse changes order only,
never original ownership. Conjugation events are deliberately not encoded. -/
def expandChronological (atoms : List (ℕ × Atom)) : List Token :=
  atoms.reverse.flatMap (fun a => expandAtom a.1 a.2)

def deleteAtom (e : ℕ) (atoms : List (ℕ × Atom)) : List (ℕ × Atom) :=
  (atoms.filter (fun a => a.1 != e)).map (fun a => (renameOwner e a.1, a.2))

def nielsenAtom : Verify.AtomicSemantics.Move → Option Atom
  | .m2 => some .a | .m3 => some .invA
  | .m4 => some .invB | .m5 => some .b
  | _ => none

/-- Explicit research-domain edit guard. Untouchedness is separate in Trace.
It neither supplies a trace nor claims a PSL/SL endpoint. -/
def DeleteAllowed (n e : ℕ) (atoms : List (ℕ × Atom)) : Prop :=
  7 ≤ n ∧ ∃ kind, (e,kind) ∈ atoms ∧ (kind = .a ∨ kind = .b)

@[simp] theorem clean_nil (e : ℕ) : clean e [] = true := rfl

@[simp] theorem clean_append (e : ℕ) (a b : List Leaf) :
    clean e (a ++ b) = (clean e a && clean e b) := by
  simp [clean]

theorem clean_iff (e : ℕ) (ls : List Leaf) :
    clean e ls = true ↔ ∀ l ∈ ls, l.owner ≠ e := by
  simp [clean]

@[simp] theorem eraseOwner_nil (e : ℕ) : eraseOwner e [] = [] := rfl

@[simp] theorem eraseOwner_append (e : ℕ) (a b : List Token) :
    eraseOwner e (a ++ b) = eraseOwner e a ++ eraseOwner e b := by
  simp [eraseOwner]

theorem eraseOwner_keep (e : ℕ) (a : Token) (h : clean e a.support = true) :
    eraseOwner e [a] = [relabelToken e a] := by
  simp [eraseOwner, h]

theorem legal_relabel (e : ℕ) (r : Rule) (a b : Token) (h : Legal r a b) :
    Legal r (relabelToken e a) (relabelToken e b) := by
  cases r <;> simpa [Legal, relabelToken] using h

theorem output_relabel (e : ℕ) (r : Rule) (a b : Token) :
    (output r a b).map (relabelToken e) =
      output r (relabelToken e a) (relabelToken e b) := by
  cases r <;> simp [output, relabelToken]

theorem eraseOwner_output (e : ℕ) (r : Rule) (a b : Token)
    (ha : clean e a.support = true) (hb : clean e b.support = true) :
    eraseOwner e (output r a b) =
      output r (relabelToken e a) (relabelToken e b) := by
  cases r <;> simp [output, eraseOwner, relabelToken, ha, hb]

/-- Replays the old rules without assuming the edited trace exists. New
numeric positions are the lengths of the filtered prefixes. -/
theorem Trace.delete_replay {start finish : List Token} {rules : List Rule}
    {history : List Leaf} (ht : Trace start rules history finish)
    (e : ℕ) (hu : clean e history = true) :
    Trace (eraseOwner e start) rules (history.map (relabelLeaf e))
      (eraseOwner e finish) := by
  induction ht with
  | nil w => exact Trace.nil _
  | step p s a b r legal tail ih =>
    simp only [clean_append, Bool.and_eq_true] at hu
    rcases hu with ⟨⟨ha, hb⟩, hh⟩
    have hi := ih hh
    have hstep := Trace.step (eraseOwner e p) (eraseOwner e s)
      (relabelToken e a) (relabelToken e b) r (legal_relabel e r a b legal)
      (by simpa only [eraseOwner_append, eraseOwner_output e r a b ha hb] using hi)
    have hepair : eraseOwner e [a,b] = [relabelToken e a, relabelToken e b] := by
      simp [eraseOwner, ha, hb]
    simpa only [eraseOwner_append, hepair, List.map_append, relabelToken] using hstep

theorem renameOwner_before (e k : ℕ) (h : k < e) : renameOwner e k = k := by
  simp [renameOwner, h]

theorem renameOwner_after (e k : ℕ) (h : e < k) : renameOwner e k = k - 1 := by
  simp [renameOwner, show ¬ k < e by omega]

theorem renameOwner_strict {e a b : ℕ} (ha : a ≠ e) (hb : b ≠ e)
    (h : a < b) : renameOwner e a < renameOwner e b := by
  unfold renameOwner
  split_ifs <;> omega

theorem renameOwner_injective {e a b : ℕ} (ha : a ≠ e) (hb : b ≠ e)
    (h : renameOwner e a = renameOwner e b) : a = b := by
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hab
  · have := renameOwner_strict ha hb hab; omega
  · have := renameOwner_strict hb ha hab; omega

@[simp] theorem relabelLeaf_tag (e : ℕ) (l : Leaf) :
    (relabelLeaf e l).tag = l.tag := rfl

theorem eraseOwner_expandAtom (e k : ℕ) (kind : Atom) :
    eraseOwner e (expandAtom k kind) =
      if k = e then [] else expandAtom (renameOwner e k) kind := by
  cases kind <;> by_cases h : k = e <;>
    simp [expandAtom, leafToken, eraseOwner, clean, relabelToken, relabelLeaf, h]

/-- Exact original-atom deletion, chronological order and reverse retained. -/
theorem eraseOwner_expandChronological (e : ℕ) (atoms : List (ℕ × Atom)) :
    eraseOwner e (expandChronological atoms) =
      expandChronological (deleteAtom e atoms) := by
  induction atoms with
  | nil => rfl
  | cons item atoms ih =>
    rcases item with ⟨k,kind⟩
    simp only [expandChronological, List.reverse_cons, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] at ih ⊢
    rw [eraseOwner_append, ih, eraseOwner_expandAtom]
    by_cases h : k = e
    · simp [deleteAtom, h]
    · simp [deleteAtom, h]

theorem deletion_replay_from_original {atoms : List (ℕ × Atom)}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : Trace (expandChronological atoms) rules history finish)
    (e : ℕ) (hu : clean e history = true) :
    Trace (expandChronological (deleteAtom e atoms)) rules
      (history.map (relabelLeaf e)) (eraseOwner e finish) := by
  simpa only [eraseOwner_expandChronological] using ht.delete_replay e hu

theorem DeleteAllowed.research_guard {n e : ℕ} {atoms : List (ℕ × Atom)}
    (h : DeleteAllowed n e atoms) : 6 ≤ n - 1 := by
  obtain ⟨hn, _⟩ := h
  omega

theorem DeleteAllowed.six_rejected (e : ℕ) (atoms : List (ℕ × Atom)) :
    ¬ DeleteAllowed 6 e atoms := by
  intro h
  obtain ⟨hn, _⟩ := h
  omega

theorem research_deletion_replay {n e : ℕ} {atoms : List (ℕ × Atom)}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (hd : DeleteAllowed n e atoms)
    (ht : Trace (expandChronological atoms) rules history finish)
    (hu : clean e history = true) :
    6 ≤ n - 1 ∧ Trace (expandChronological (deleteAtom e atoms)) rules
      (history.map (relabelLeaf e)) (eraseOwner e finish) :=
  ⟨hd.research_guard, deletion_replay_from_original ht e hu⟩

/-- Canonical original owners in chronological Nielsen order. -/
def numberFrom : ℕ → List Atom → List (ℕ × Atom)
  | _, [] => []
  | k, kind :: rest => (k,kind) :: numberFrom (k + 1) rest

@[simp] theorem numberFrom_length (k : ℕ) (w : List Atom) :
    (numberFrom k w).length = w.length := by
  induction w generalizing k with
  | nil => rfl
  | cons kind rest ih => simp [numberFrom, ih]

theorem deleteAtom_cons (e k : ℕ) (kind : Atom) (rest : List (ℕ × Atom)) :
    deleteAtom e ((k,kind) :: rest) =
      if k = e then deleteAtom e rest
      else (renameOwner e k,kind) :: deleteAtom e rest := by
  by_cases h : k = e <;> simp [deleteAtom, h]

theorem deleteAtom_numberFrom_after (e k : ℕ) (w : List Atom) (h : e < k) :
    deleteAtom e (numberFrom k w) = numberFrom (k - 1) w := by
  induction w generalizing k with
  | nil => rfl
  | cons kind rest ih =>
    simp only [numberFrom, deleteAtom_cons]
    rw [ite_eq_right (by omega), renameOwner_after e k h, ih (k + 1) (by omega)]
    congr 1
    congr 1
    omega

/-- Removes exactly the occurrence at the original index pre.length. It does
not remove all equal *values*, and the renumbering is constructed, not supplied. -/
theorem deleteAtom_numberFrom_split (k : ℕ) (pre post : List Atom) (kind : Atom) :
    deleteAtom (k + pre.length) (numberFrom k (pre ++ kind :: post)) =
      numberFrom k (pre ++ post) := by
  induction pre generalizing k with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero, numberFrom,
      deleteAtom_cons]
    simp only [ite_true]
    simpa only [Nat.add_sub_cancel] using
      deleteAtom_numberFrom_after k (k + 1) post (by omega)
  | cons first pre ih =>
    simp only [List.cons_append, numberFrom, List.length_cons, deleteAtom_cons]
    rw [ite_eq_right (by omega), renameOwner_before _ _ (by omega)]
    have he : k + (pre.length + 1) = (k + 1) + pre.length := by omega
    rw [he, ih]

theorem numbered_deletion_replay (pre post : List Atom) (kind : Atom)
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : Trace (expandChronological (numberFrom 0 (pre ++ kind :: post)))
      rules history finish)
    (hu : clean pre.length history = true) :
    Trace (expandChronological (numberFrom 0 (pre ++ post))) rules
      (history.map (relabelLeaf pre.length)) (eraseOwner pre.length finish) := by
  have h := deletion_replay_from_original ht pre.length hu
  have hr := deleteAtom_numberFrom_split 0 pre post kind
  simp only [Nat.zero_add] at hr
  rw [hr] at h
  exact h

def leaves (w : List Token) : List Leaf := w.flatMap Token.support

/-- Surviving supports are a sublist of the old supports, even for mergers. -/
theorem leaves_step_sublist (p s : List Token) (a b : Token) (r : Rule) :
    (leaves (p ++ output r a b ++ s)).Sublist (leaves (p ++ [a,b] ++ s)) := by
  have h : (leaves (output r a b)).Sublist (a.support ++ b.support) := by
    cases r <;> simp [leaves, output]
  simpa [leaves, List.append_assoc] using
    (List.Sublist.refl (leaves p)).append (h.append (List.Sublist.refl (leaves s)))

theorem Trace.leaves_sublist {start finish : List Token} {rules : List Rule}
    {history : List Leaf} (ht : Trace start rules history finish) :
    (leaves finish).Sublist (leaves start) := by
  induction ht with
  | nil => exact List.Sublist.refl _
  | step p s a b r _ _ ih => exact ih.trans (leaves_step_sublist p s a b r)

theorem Trace.no_duplicate_leaves {start finish : List Token} {rules : List Rule}
    {history : List Leaf} (ht : Trace start rules history finish)
    (h : (leaves start).Nodup) : (leaves finish).Nodup :=
  h.sublist ht.leaves_sublist

def factorTag : Factor → Tag
  | .sigma => .sigma
  | .rho | .rhoInv => .rho

def TypedToken (t : Token) : Prop :=
  t.support ≠ [] ∧ ∀ l ∈ t.support, l.tag = factorTag t.value

def TypedState (w : List Token) : Prop := ∀ t ∈ w, TypedToken t

theorem typed_output (r : Rule) (a b : Token) (hl : Legal r a b)
    (ha : TypedToken a) (hb : TypedToken b) : TypedState (output r a b) := by
  cases r <;> simp only [output, TypedState, List.mem_singleton, List.not_mem_nil,
    false_implies, implies_true]
  all_goals
    intro t ht
    subst t
    obtain ⟨_, _, hva, hvb⟩ := hl
    constructor
    · intro he
      exact ha.1 (List.append_eq_nil_iff.mp he).1
    · intro l hm
      rcases List.mem_append.mp hm with hm | hm
      · simpa only [hva, factorTag] using ha.2 l hm
      · simpa only [hvb, factorTag] using hb.2 l hm

theorem Trace.typed_preserved {start finish : List Token} {rules : List Rule}
    {history : List Leaf} (ht : Trace start rules history finish)
    (hw : TypedState start) : TypedState finish := by
  induction ht with
  | nil => exact hw
  | step p s a b r legal tail ih =>
    apply ih
    intro t hm
    simp only [List.mem_append] at hm
    rcases hm with (hp | ho) | hs
    · exact hw t (by simp [hp])
    · exact typed_output r a b legal (hw a (by simp)) (hw b (by simp)) t ho
    · exact hw t (by simp [hs])

theorem expandChronological_typed (atoms : List (ℕ × Atom)) :
    TypedState (expandChronological atoms) := by
  intro t ht
  obtain ⟨item, _, hm⟩ := List.mem_flatMap.mp ht
  rcases item with ⟨k,kind⟩
  cases kind <;> simp [expandAtom, leafToken] at hm <;>
    rcases hm with rfl | rfl <;> simp [TypedToken, factorTag]

theorem nielsen_ids :
    nielsenAtom .m2 = some .a ∧ nielsenAtom .m3 = some .invA ∧
    nielsenAtom .m4 = some .invB ∧ nielsenAtom .m5 = some .b := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem excluded_ids :
    nielsenAtom .m0 = none ∧ nielsenAtom .m1 = none ∧
    nielsenAtom .m6 = none ∧ nielsenAtom .m7 = none ∧
    nielsenAtom .m8 = none ∧ nielsenAtom .m9 = none ∧
    nielsenAtom .m10 = none ∧ nielsenAtom .m11 = none ∧
    nielsenAtom .m12 = none ∧ nielsenAtom .m13 = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Historical marks, not marks reconstructed from the final live tokens. -/
def marks (tag : Tag) (history : List Leaf) : Finset ℕ :=
  ((history.filter (fun l => l.tag == tag)).map Leaf.owner).toFinset

def allMarks (history : List Leaf) : Finset ℕ :=
  (history.map Leaf.owner).toFinset

theorem mem_marks_iff (e : ℕ) (tag : Tag) (history : List Leaf) :
    e ∈ marks tag history ↔ ∃ l ∈ history, l.owner = e ∧ l.tag = tag := by
  simp only [marks, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  aesop

theorem clean_iff_not_marked (e : ℕ) (history : List Leaf) :
    clean e history = true ↔ e ∉ allMarks history := by
  simp [clean, allMarks]

theorem allMarks_union (history : List Leaf) :
    allMarks history = marks .sigma history ∪ marks .rho history := by
  ext e
  simp only [allMarks, List.mem_toFinset, List.mem_map, Finset.mem_union,
    mem_marks_iff]
  constructor
  · rintro ⟨l, hl, he⟩
    cases ht : l.tag with
    | sigma => exact Or.inl ⟨l, hl, he, ht⟩
    | rho => exact Or.inr ⟨l, hl, he, ht⟩
  · rintro (⟨l, hl, he, _⟩ | ⟨l, hl, he, _⟩) <;> exact ⟨l, hl, he⟩

end Candidate.ShortWordDelete

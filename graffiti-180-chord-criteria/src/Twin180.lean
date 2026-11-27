import GadgetTools180

set_option warningAsError true
namespace Converse180
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

abbrev Twin (V : Type*) := (V ⊕ V) ⊕ Unit
noncomputable def copy (i : Bool) (v : V) : Twin V := if i then .inl (.inr v) else .inl (.inl v)
noncomputable def hub : Twin V := .inr ()
noncomputable def twin (r : V) : SimpleGraph (Twin V) where
  Adj := Sum.elim (Sum.elim
    (fun a => Sum.elim (Sum.elim (G.Adj a) (fun _ => False)) (fun _ => a=r))
    (fun a => Sum.elim (Sum.elim (fun _ => False) (G.Adj a)) (fun _ => a=r)))
    (fun _ => Sum.elim (Sum.elim (fun a => r=a) (fun a => r=a)) (fun _ => False))
  symm := by rintro ((a|a)|a) ((b|b)|b) e <;> first | exact e.symm | exact e.elim
  loopless := by rintro ((a|a)|a) e <;> first | exact G.loopless _ e | exact e

noncomputable def projectCopy (i : Bool) (r : V) : Twin V → V :=
  Sum.elim (Sum.elim (fun a => if i then r else a) (fun a => if i then a else r)) (fun _ => r)
noncomputable def inCopy (i : Bool) : Twin V → Prop :=
  Sum.elim (Sum.elim (fun _ => i=false) (fun _ => i=true)) (fun _ => False)

omit [Fintype V] [DecidableEq V] in
theorem copy_inj (i : Bool) : Function.Injective (copy (V:=V) i) := by
  intro v w e
  cases i <;> simpa [copy] using e

omit [Fintype V] [DecidableEq V] in
theorem twin_map (r : V) (i : Bool) {v w : V} :
    (twin G r).Adj (copy i v) (copy i w) ↔ G.Adj v w := by cases i <;> rfl

omit [Fintype V] [DecidableEq V] in
theorem twin_rim {r : V} {T : SimpleGraph (Twin V)} (sub : T ≤ twin G r)
    (tc : T.Connected) (i : Bool) : T.Adj (copy i r) hub := by
  apply forced_edge T tc _ _ (inCopy i)
  · cases i <;> rfl
  · exact id
  · rintro ((a|a)|a) ((b|b)|b) e ha hb
    all_goals have base := sub e
    all_goals cases i <;> simp_all [twin,inCopy,copy,hub]

theorem twin_leaves (r : V) (hn : 1 < Fintype.card V) :
    maxLeaves (twin G r) ≤ 2 * weightedLeaves G (univ.erase r) := by
  classical
  apply Finset.sup_le
  intro T ht
  obtain ⟨st,tr⟩ := (mem_filter.mp ht).2
  have rim := twin_rim G st tr.isConnected
  have noHub : hub ∉ leaves T := by
    intro h
    have eq := leaf_unique T h (rim false).symm (rim true).symm
    simp [copy] at eq
  have each (i : Bool) : (pull (copy i) (leaves T)).card ≤ weightedLeaves G (univ.erase r) := by
    have step {a b : Twin V} (e : T.Adj a b) : projectCopy i r a = projectCopy i r b ∨
        T.Adj (copy i (projectCopy i r a)) (copy i (projectCopy i r b)) := by
      have h := st e
      rcases a with (a|a)|a <;> rcases b with (b|b)|b <;> cases i <;>
        simp_all [twin,projectCopy,copy]
    have left : Function.LeftInverse (projectCopy i r) (copy i) := by intro v; cases i <;> rfl
    obtain ⟨K,ks,kt,map⟩ := tree_inside G T tr.isConnected (copy i) (projectCopy i r) left
      (fun h => step h) (fun {_ _} e => (twin_map G r i).mp (st e))
    have ex (v : V) (_ : v ∈ (univ : Finset V)) (out : v ∉ univ.erase r) :
        ∃ w, T.Adj (copy i v) w ∧ ∀ u : V, w ≠ copy i u := by
      have eq : v=r := by simpa using out
      subst v
      exact ⟨hub,rim i,fun u => by cases i <;> simp [hub,copy]⟩
    simpa using piece_leaves G hn T (copy i) (copy_inj i) ks kt map _ _ ex
  have card (S : Finset (Twin V)) : S.card =
      (pull (copy false) S).card + (pull (copy true) S).card +
      (pull (Sum.inr : Unit → Twin V) S).card := by
    have e0 : pull Sum.inl (pull Sum.inl S) = pull (copy false) S := by ext v; simp [copy]
    have e1 : pull Sum.inr (pull Sum.inl S) = pull (copy true) S := by ext v; simp [copy]
    calc S.card = _ := split_card S
         _ = _ := by rw [split_card (pull Sum.inl S),e0,e1]
  have empty : pull (Sum.inr : Unit → Twin V) (leaves T) = ∅ := by
    ext x; cases x; simpa [hub] using noHub
  have c := card (leaves T)
  rw [empty,card_empty] at c
  have a := each false
  have b := each true
  omega

theorem twin_bip (r : V) : bipartiteNum (twin G r) ≤ 2*bipartiteNum G+1 := by
  classical
  apply Finset.sup_le
  intro S h
  have each (i : Bool) : (pull (copy i) S).card ≤ bipartiteNum G := le_sup (f := card)
    (mem_filter.mpr ⟨mem_univ _,restrict_color G (twin G r) (copy i) (copy_inj i)
      (fun e => (twin_map G r i).mpr e) (mem_filter.mp h).2⟩)
  have e0 : pull Sum.inl (pull Sum.inl S) = pull (copy false) S := by ext v; simp [copy]
  have e1 : pull Sum.inr (pull Sum.inl S) = pull (copy true) S := by ext v; simp [copy]
  have c := split_card S
  rw [split_card (pull Sum.inl S),e0,e1] at c
  have one := card_le_univ (pull (Sum.inr : Unit → Twin V) S)
  rw [Fintype.card_unit] at one
  have a := each false
  have b := each true
  omega

noncomputable def twinSet (S : Finset V) (center : Bool) : Finset (Twin V) :=
  (S.disjSum S).disjSum (if center then univ else ∅)

omit [Fintype V] [DecidableEq V] in
theorem twinSet_card (S : Finset V) (b : Bool) : (twinSet S b).card = 2*S.card+b.toNat := by
  cases b <;> simp [twinSet,two_mul]

omit [Fintype V] [DecidableEq V] in
theorem twin_indep (r : V) (A : Finset V) (ai : Indep G A) (center : Bool)
    (ok : center=true → r ∉ A) : Indep (twin G r) (twinSet A center) := by
  rintro ((v|v)|v) hv ((w|w)|w) hw ne e
  all_goals cases center <;> simp_all [twinSet,twin]
  all_goals exact ai _ hv _ hw ne e

#print axioms twin_leaves
#print axioms twin_bip
#print axioms twin_indep
end Converse180

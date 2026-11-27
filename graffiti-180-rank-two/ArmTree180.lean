import SingleArm180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extend a descending tree on D, an attachment to w and a further edge
outside D, preserving a specified farthest noninitial vertex as a leaf.
The initial vertex may be the root itself. -/
theorem arm_tree_in {G J : SimpleGraph V} (jg : J≤G) (nc : NoCut G) (hn : 1<Fintype.card V)
    {r t w a b v : V} {D : Finset V} (td : t∈D)
    (prior : ∀ i∈D, i≠t → ∃ q∈D, Arc J r q i)
    (vd : v∈D) (vt : v≠t) (last : ∀ i∈D,J.dist i r≤J.dist v r)
    (wd : w∉D) (tw : G.Adj t w) (ad : a∉D) (bd : b∉D) (aw : a≠w) (ab : G.Adj a b) :
    ∃ T≤G, T.IsTree ∧ T.Adj t w ∧ (∀ i∈D, i≠t → ∀ q, Arc J r q i → T.Adj i q) ∧ T.Adj a b ∧ (∃ v∈D,v≠t ∧ v∈leaves T) ∧
      ∃ p : V→V, ∃ d : V→ℕ, ∀ i∈D, T.Adj i (p i) ∧ (p i∈D ∨ p i=w) ∧ d (p i)<d i := by
  classical
  let p (i : V) := if id : i∈D then if it : i=t then w else (prior i id it).choose else if i=a then b else w
  let d (i : V) := if i∈D then J.dist i r+3 else if i=w then 0 else if i=a then 2 else 1
  have tip : p t=w := by simp [p,td]
  have regular {i : V} (id : i∈D) (it : i≠t) : p i∈D ∧ Arc J r (p i) i := by
    simpa [p,id,it] using (prior i id it).choose_spec
  have decrease (i : V) (iw : i≠w) : d (p i)<d i := by
    by_cases id : i∈D
    · by_cases it : i=t
      · subst i; simp [tip,d,wd,td]
      · have ⟨pd,step⟩ := regular id it
        simp only [d,if_pos pd,if_pos id]
        have := step.2.1
        omega
    · by_cases ia : i=a
      · subst i
        by_cases bw : b=w <;> simp [p,d,ad,bd,aw,bw,ab.ne.symm,wd]
      · simp [d,p,id,ia,iw,wd]
  obtain ⟨K,kt,target⟩ := virtual_tree w p d decrease
  have live {i : V} (id : i∈D) : G.Adj i (p i) := by
    by_cases it : i=t
    · subst i; simpa only [tip] using tw
    · exact jg (regular id it).2.1.symm
  let H := prune G v {p v}
  obtain ⟨M,mh,tree,keep⟩ := keep_target H K (prune_one G nc (live vd)) kt
  have lift (i : V) (id : i∈D) : M.Adj i (p i) := by
    apply keep
    refine ⟨?_,target i (fun iw => wd (iw ▸ id))⟩
    by_cases iv : i=v
    · subst i; exact prune_spoke (live vd) (mem_singleton_self _)
    apply prune_away iv _ (live id)
    by_cases it : i=t
    · subst i; rw [tip]; exact fun eq => wd (eq ▸ vd)
    have step := (regular id it).2.2.1
    have hi := last i id
    intro eq
    rw [eq] at step
    omega
  have pab : p a=b := by simp [p,ad]
  have mab : M.Adj a b := keep ⟨prune_away (fun eq => ad (eq ▸ vd)) (fun eq => bd (eq ▸ vd)) ab,
    pab ▸ target a aw⟩
  have leaf : v∈leaves M := leaf_of_unique M tree.isConnected hn v (fun {i j} vi vj =>
    (mem_singleton.mp ((mh vi).2.1 rfl)).trans (mem_singleton.mp ((mh vj).2.1 rfl)).symm)
  have fixed {i : V} (id : i∈D) (it : i≠t) {q : V} (qi : Arc J r q i) : M.Adj i q := by
    have reg := (regular id it).2
    exact qi.2.2 _ reg.1 reg.2.1 ▸ lift i id
  refine ⟨M,mh.trans (prune_le ..),tree,tip ▸ lift t td,fun _ id it _ qi => fixed id it qi,mab,⟨v,vd,vt,leaf⟩,p,d,fun i id => ⟨lift i id,?_,decrease i (fun eq => wd (eq ▸ id))⟩⟩
  by_cases it : i=t
  · exact Or.inr (it ▸ tip)
  · exact Or.inl (regular id it).1


/-- Extend a descending tree on D, an attachment to w and a further edge
outside D, preserving a specified farthest noninitial vertex as a leaf.
The initial vertex may be the root itself. -/
theorem arm_tree {G : SimpleGraph V} (nc : NoCut G) (hn : 1<Fintype.card V)
    {r t w a b v : V} {D : Finset V} (td : t∈D)
    (prior : ∀ i∈D, i≠t → ∃ q∈D, Arc G r q i)
    (vd : v∈D) (vt : v≠t) (last : ∀ i∈D,G.dist i r≤G.dist v r)
    (wd : w∉D) (tw : G.Adj t w) (ad : a∉D) (bd : b∉D) (aw : a≠w) (ab : G.Adj a b) :
    ∃ T≤G, T.IsTree ∧ T.Adj t w ∧ (∀ i∈D, i≠t → ∀ q, Arc G r q i → T.Adj i q) ∧ T.Adj a b ∧ (∃ v∈D,v≠t ∧ v∈leaves T) ∧
      ∃ p : V→V, ∃ d : V→ℕ, ∀ i∈D, T.Adj i (p i) ∧ (p i∈D ∨ p i=w) ∧ d (p i)<d i :=
  arm_tree_in le_rfl nc hn td prior vd vt last wd tw ad bd aw ab

#print axioms arm_tree_in
#print axioms arm_tree
end Minimal180.RootEar

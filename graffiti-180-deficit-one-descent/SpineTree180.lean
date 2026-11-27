import Spine180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem prune_one (G : SimpleGraph V) (nc : NoCut G) {v p : V} (e : G.Adj v p) :
    (prune G v {p}).Connected := by
  classical
  let H := prune G v {p}
  let W := ↥({v}ᶜ : Set V)
  let f : G.induce ({v}ᶜ : Set V) →g H :=
    ⟨Subtype.val,fun {a b} ab => prune_away a.property b.property ab⟩
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨v,fun z => ?_⟩
  by_cases eq : z=v
  · exact eq ▸ Reachable.refl _
  · have vp : H.Adj v p := prune_spoke e (mem_singleton_self _)
    exact vp.reachable.trans ((nc v (⟨p,e.ne.symm⟩ : W) ⟨z,eq⟩).map f)

/-- Extend the descending spine, its attachment to w and a disjoint extra
edge, keeping the last disagreement a leaf in the upper block. The edges
indexed by the spine all descend in the supplied auxiliary height. -/
theorem spine_tree {G J : SimpleGraph V} (jg : J≤G) (nc : NoCut G) (hn : 1<Fintype.card V)
    {r t w a b : V} {D : Finset V} (sp : Spine J r D t) (wd : w∉D)
    (tw : G.Adj t w) (ad : a∉D) (bd : b∉D) (aw : a≠w) (ab : G.Adj a b) :
    ∃ T≤G, T.IsTree ∧ T.Adj a b ∧ (∃ v∈D,v∈leaves T) ∧
      ∃ p : V→V, ∃ d : V→ℕ, ∀ i∈D, T.Adj i (p i) ∧ (p i∈D ∨ p i=w) ∧ d (p i)<d i := by
  classical
  obtain ⟨v,vd,vt,last⟩ := sp.last_step
  let p (i : V) := if id : i∈D then if it : i=t then w else (sp.prior i id it).choose else if i=a then b else w
  let d (i : V) := if i∈D then J.dist i r+3 else if i=w then 0 else if i=a then 2 else 1
  have tip : p t=w := by simp [p,sp.tip]
  have regular {i : V} (id : i∈D) (it : i≠t) : p i∈D ∧ Arc J r (p i) i := by
    simpa [p,id,it] using (sp.prior i id it).choose_spec
  have decrease (i : V) (iw : i≠w) : d (p i)<d i := by
    by_cases id : i∈D
    · by_cases it : i=t
      · subst i; simp [tip,d,wd,sp.tip]
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
  refine ⟨M,mh.trans (prune_le ..),tree,mab,⟨v,vd,leaf⟩,p,d,fun i id => ⟨lift i id,?_,decrease i (fun eq => wd (eq ▸ id))⟩⟩
  by_cases it : i=t
  · exact Or.inr (it ▸ tip)
  · exact Or.inl (regular id it).1

#print axioms spine_tree
end Minimal180.DescentOne

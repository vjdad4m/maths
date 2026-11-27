import RetainBags180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

omit [Fintype V] in
theorem Bags.colorDown {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B} (h : Bags H G f) (W : Finset V)
    (col : TwoColor H W) : TwoColor G (W.image f) := by
  classical
  have pick (i : B) : ∃ x,f x=i ∧ (x∈W ↔ i∈W.image f) := by
    by_cases im : i∈W.image f
    · obtain ⟨x,xw,eq⟩ := mem_image.mp im
      exact ⟨x,eq,iff_of_true xw im⟩
    · obtain ⟨x,eq⟩ := h.onto i
      exact ⟨x,eq,iff_of_false (fun xw => im (eq ▸ mem_image_of_mem _ xw)) im⟩
  choose s sec membership using pick
  have left : Function.LeftInverse f s := sec
  have eq : pull s W=W.image f := by ext i; exact mem_pull.trans (membership i)
  rw [←eq]
  exact restrict_color G H s left.injective (fun e => (h.repHom s left).map_adj e) col

noncomputable abbrev Copies (D : Finset V) := ↥D × Fin (Fintype.card V)
noncomputable abbrev Forced (D : Finset V) := V ⊕ Copies D
noncomputable def forget (D : Finset V) : Forced D→V := Sum.elim id (fun z => z.1.val)
noncomputable def force (G : SimpleGraph V) (D : Finset V) : SimpleGraph (Forced D) := G.comap (forget D)

omit [DecidableEq V] in
theorem force_bags (G : SimpleGraph V) (D : Finset V) : Bags (force G D) G (forget D) :=
  ⟨fun i => ⟨.inl i,rfl⟩,fun _ => Iff.rfl⟩

theorem pulled_size (D X : Finset V) (inc : D⊆X) :
    (pull (forget D) X).card=X.card+Fintype.card (Copies D) := by
  classical
  have eq : pull (forget D) X=X.disjSum univ := by
    ext v
    cases v with
    | inl _ => simp [forget]
    | inr z => simp [forget,inc z.1.property]
  rw [eq,card_disjSum,card_univ]

theorem forced_indep (G : SimpleGraph V) (D A : Finset V) (ai : Indep G A) :
    Indep (force G D) (pull (forget D) A) := by
  intro x xm y ym _ edge
  have e : G.Adj (forget D x) (forget D y) := edge
  exact ai _ (mem_pull.mp xm) _ (mem_pull.mp ym) e.ne e

/-- Every largest induced bipartite witness upstairs projects to a
bipartite set containing the entire forced independent set D downstairs.
There are n extra independent copies per forced vertex, where n is the
order of the original graph. -/
theorem forced_max (G : SimpleGraph V) (D : Finset V) (di : Indep G D) (W : Finset (Forced D))
    (col : TwoColor (force G D) W) (opt : W.card=bipartiteNum (force G D)) :
    let Z := W.image (forget D)
    TwoColor G Z ∧ D⊆Z ∧ W.card≤Z.card+Fintype.card (Copies D) := by
  classical
  intro Z
  let X := pull (Sum.inl : V→Forced D) W
  let Y := pull (Sum.inr : Copies D→Forced D) W
  have count : W.card=X.card+Y.card := split_card W
  have xz : X⊆Z := fun i im => mem_image.mpr ⟨.inl i,mem_pull.mp im,rfl⟩
  have capY := card_le_univ Y
  have xs := card_le_card xz
  refine ⟨(force_bags G D).colorDown W col,?_,by omega⟩
  intro i id
  by_contra missing
  have xi : i∉X := fun im => missing (xz im)
  have smallX := card_le_univ (insert i X)
  rw [card_insert_of_not_mem xi] at smallX
  let j : ↥D := ⟨i,id⟩
  let ins (k : Fin (Fintype.card V)) : Copies D := (j,k)
  let E := univ.image ins
  have ec : E.card=Fintype.card V := by
    rw [show E=univ.image ins from rfl,card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]
    simp
  have dis : Disjoint E Y := by
    apply disjoint_left.mpr
    intro z ze zy
    obtain ⟨k,_,rfl⟩ := mem_image.mp ze
    exact missing (mem_image.mpr ⟨.inr (ins k),mem_pull.mp zy,rfl⟩)
  have sum := card_le_univ (E∪Y)
  rw [card_union_of_disjoint dis,ec] at sum
  have low := bip_bound (force G D) (forced_indep G D D di) (show Indep (force G D) ∅ by simp [Indep])
    (show Disjoint (pull (forget D) D) ∅ by simp)
  rw [pulled_size D D (Subset.rfl),card_empty,add_zero,←opt] at low
  omega

#print axioms Bags.colorDown
#print axioms pulled_size
#print axioms forced_indep
#print axioms forced_max
end Minimal180.Substitution

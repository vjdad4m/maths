import SingleSplit180

set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The component of a vertex in a retained set. -/
noncomputable def part (J : SimpleGraph V) (R : Finset V) (a : V) : Finset V := by
  classical
  exact R.filter fun t => (within J R).Reachable a t

omit [Fintype V] [DecidableEq V] in
theorem mem_part (J : SimpleGraph V) (R : Finset V) (a t : V) :
    t∈part J R a ↔ t∈R ∧ (within J R).Reachable a t := by
  classical
  simp [part]

omit [Fintype V] [DecidableEq V] in
theorem part_eq_of_reach (J : SimpleGraph V) (R : Finset V) {a b : V}
    (reach : (within J R).Reachable a b) : part J R a=part J R b := by
  ext t
  rw [mem_part,mem_part]
  exact and_congr_right fun _ => ⟨fun h => reach.symm.trans h,fun h => reach.trans h⟩

omit [Fintype V] in
/-- Components of the retained old core other than the component of the other tip. -/
noncomputable def remote (J : SimpleGraph V) (R : Finset V) (y : V) : Finset (Finset V) :=
  (R.image (part J R)).erase (part J R y)

omit [Fintype V] in
/-- Proposed leaves which lack both a retained old neighbor and an edge to the returned tip. -/
noncomputable def demand (J : SimpleGraph V) (R C Z : Finset V) (x : V) : Finset V := by
  classical
  exact (C.erase x ∪ Z).filter fun q => ¬Dominates J R q ∧ ¬J.Adj q x

omit [Fintype V] in
theorem mem_demand (J : SimpleGraph V) (R C Z : Finset V) (x q : V) :
    q∈demand J R C Z x ↔ q∈C.erase x∪Z ∧ ¬Dominates J R q ∧ ¬J.Adj q x := by
  classical
  simp only [demand,mem_filter]

/-- Distinct returned old leaves may serve multiple component and domination
requirements. Every returned vertex in this version is an old neighbor of x. -/
theorem first_of_return_set (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C B Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (bc : B⊆C.erase x) (zs : Z⊆(U\C).erase y)
    (gain : B.card<Z.card) (links : ∀ b∈B,J.Adj x b)
    (join : ∀ H∈remote J ((univ\C)\Z) y,∃ b∈B,Dominates J H b)
    (serve : ∀ q∈demand J ((univ\C)\Z) C Z x,q∈B ∨ Dominates J B q) :
    FirstForm J U x y w := by
  classical
  let R := (univ\C)\Z
  have yr : y∈R := mem_sdiff.mpr ⟨tip.2.1,fun h => (mem_erase.mp (zs h)).1 rfl⟩
  apply first_of_local_split J hc hn x y w xy old xw wy U C B Z cu count tip bc zs gain
  · apply (connected_cuts J (insert x B)).mpr
    refine ⟨⟨x,mem_insert_self ..⟩,?_⟩
    intro f good
    have same (a : V) (ha : a∈insert x B) : f a=f x := by
      rcases mem_insert.mp ha with e|aB
      · rw [e]
      · exact (good x (mem_insert_self ..) a ha (links a aB)).symm
    exact fun a ha b hb => (same a ha).trans (same b hb).symm
  · dsimp only
    intro a ar
    by_cases eq : part J R a=part J R y
    · have mem : y∈part J R a := eq ▸ (mem_part J R y y).mpr ⟨yr,.refl _⟩
      exact ⟨y,yr,((mem_part ..).mp mem).2,Or.inl rfl⟩
    · have hr : part J R a∈remote J R y := mem_erase.mpr ⟨eq,mem_image_of_mem _ ar⟩
      obtain ⟨b,hb,t,ht,bt⟩ := join _ hr
      obtain ⟨tr,at'⟩ := (mem_part ..).mp ht
      exact ⟨t,tr,at',Or.inr ⟨b,mem_insert_of_mem hb,bt.symm⟩⟩
  · dsimp only
    intro q hl
    by_cases qr : Dominates J R q
    · exact Or.inl qr
    right
    by_cases qx : J.Adj q x
    · exact ⟨x,mem_insert_self ..,qx⟩
    have inc : q∈C.erase x∪Z := (union_subset_union_left (sdiff_subset : C.erase x\B⊆C.erase x)) hl
    have nb : q∉B := by
      rcases mem_union.mp hl with h|h
      · exact (mem_sdiff.mp h).2
      · exact fun k => (mem_sdiff.mp (mem_of_mem_erase (zs h))).2 (mem_of_mem_erase (bc k))
    obtain k|⟨b,hb,e⟩ := serve q ((mem_demand ..).mpr ⟨inc,qr,qx⟩)
    · exact (nb k).elim
    · exact ⟨b,mem_insert_of_mem hb,e⟩

/-- A cardinal sufficient condition requiring no enumeration of returned
sets. Each remote component and each remaining domination demand may select
one old neighbor of x; the union of these selections fits in the budget. -/
theorem first_of_requirement_budget (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zs : Z⊆(U\C).erase y)
    (budget : (remote J ((univ\C)\Z) y).card+(demand J ((univ\C)\Z) C Z x).card<Z.card)
    (join : ∀ H∈remote J ((univ\C)\Z) y,∃ b∈C.erase x,J.Adj x b ∧ Dominates J H b)
    (serve : ∀ q∈demand J ((univ\C)\Z) C Z x,∃ b∈C.erase x,J.Adj x b ∧ (q=b ∨ J.Adj q b)) :
    FirstForm J U x y w := by
  classical
  let R := (univ\C)\Z
  let K := remote J R y
  let D := demand J R C Z x
  let f (H : Finset V) := if h : H∈K then (join H h).choose else x
  let g (q : V) := if h : q∈D then (serve q h).choose else x
  have hf (H : Finset V) (h : H∈K) : f H∈C.erase x ∧ J.Adj x (f H) ∧ Dominates J H (f H) := by
    simpa only [f,dif_pos h] using (join H h).choose_spec
  have hg (q : V) (h : q∈D) : g q∈C.erase x ∧ J.Adj x (g q) ∧ (q=g q ∨ J.Adj q (g q)) := by
    simpa only [g,dif_pos h] using (serve q h).choose_spec
  let B := K.image f ∪ D.image g
  have use (b : V) (hb : b∈B) : b∈C.erase x ∧ J.Adj x b := by
    rcases mem_union.mp hb with hf'|hg'
    · obtain ⟨H,h,rfl⟩ := mem_image.mp hf'
      exact ⟨(hf H h).1,(hf H h).2.1⟩
    · obtain ⟨q,h,rfl⟩ := mem_image.mp hg'
      exact ⟨(hg q h).1,(hg q h).2.1⟩
  have limit : B.card≤K.card+D.card :=
    (card_union_le ..).trans (Nat.add_le_add card_image_le card_image_le)
  apply first_of_return_set J hc hn x y w xy old xw wy U C B Z cu count tip
    (fun _ h => (use _ h).1) zs (limit.trans_lt budget) (fun _ h => (use _ h).2)
  · intro H h
    exact ⟨f H,mem_union_left _ (mem_image_of_mem f h),(hf H h).2.2⟩
  · intro q h
    have gb : g q∈B := mem_union_right _ (mem_image_of_mem g h)
    rcases (hg q h).2.2 with e|edge
    · exact Or.inl (e ▸ gb)
    · exact Or.inr ⟨g q,gb,edge⟩

#print axioms first_of_return_set
#print axioms first_of_requirement_budget
end Minimal180.Controlled

import BridgePair180

set_option warningAsError true
namespace Minimal180.PrivateCore
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Controlled
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary certificate leaves whose sole old-core neighbor is z. -/
noncomputable def privateLeaves (J : SimpleGraph V) (C : Finset V) (x z : V) : Finset V := by
  classical
  exact (C.erase x).filter fun q => J.Adj q z ∧ ∀ a∈univ\C, J.Adj q a → a=z

theorem private_iff (J : SimpleGraph V) (C : Finset V) (x z q : V) :
    q∈privateLeaves J C x z ↔ q∈C.erase x ∧ J.Adj q z ∧ ∀ a∈univ\C, J.Adj q a → a=z := by
  classical
  simp [privateLeaves]

/-- Success of the specified one-for-one exchange in the graph with the chord. -/
def SingleWorks (J : SimpleGraph V) (C : Finset V) (x y z : V) : Prop :=
  let L := insert z (C.erase x)
  let G := J⊔SimpleGraph.edge x y
  Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q

/-- Within the old graph, distance at most two from x, including x. -/
def NearTwo (J : SimpleGraph V) (x q : V) : Prop :=
  q=x ∨ J.Adj x q ∨ ∃ b,J.Adj x b ∧ J.Adj b q

private theorem retained_or_private (J : SimpleGraph V) (C : Finset V) (x y z q : V)
    (tip : NeedsTip J C (univ\C) x y) (qc : q∈C.erase x) :
    Dominates J ((univ\C).erase z) q ∨ q∈privateLeaves J C x z := by
  classical
  by_cases d : Dominates J ((univ\C).erase z) q
  · exact Or.inl d
  have unique (a : V) (ha : a∈univ\C) (qa : J.Adj q a) : a=z := by
    by_contra ne
    exact d ⟨a,mem_erase.mpr ⟨ne,ha⟩,qa⟩
  obtain ⟨a,ha,qa⟩ := tip.2.2.2.2 q (mem_of_mem_erase qc) (mem_erase.mp qc).1
  exact Or.inr ((private_iff ..).mpr ⟨qc,unique a ha qa ▸ qa,unique⟩)

/-- Lower optimality forbids a surviving old neighbor of x from covering every
private leaf of a removable eligible vertex. Replacing z by b would give the
lower graph as many eligible leaves as the upper certificate. -/
theorem old_anchor_obstruction (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (U C : Finset V) (x y z b : V) (cu : C⊆U) (ct : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zu : z∈(U\C).erase y)
    (conn : Con J ((univ\C).erase z)) (xb : J.Adj x b)
    (survives : Dominates J ((univ\C).erase z) b) :
    ∃ q∈privateLeaves J C x z, q≠b ∧ ¬J.Adj b q := by
  classical
  let S := univ\C
  let R := S.erase z
  have zy := (mem_erase.mp zu).1
  obtain ⟨zU,zC⟩ := mem_sdiff.mp (mem_of_mem_erase zu)
  have zs : z∈S := mem_sdiff.mpr ⟨mem_univ _,zC⟩
  have bC : b∈C := by
    by_contra nb
    exact tip.2.2.2.1 ⟨b,mem_sdiff.mpr ⟨mem_univ _,nb⟩,xb⟩
  obtain ⟨r,hr,br⟩ := survives
  have joined : Con J (insert b R) := con_insert J conn hr br
  obtain ⟨i,hi,j,hj,ij⟩ := component_exit J S {z} tip.2.2.1 z y zs (mem_singleton_self _)
    (mem_sdiff.mpr ⟨tip.2.1,fun h => zy (mem_singleton.mp h).symm⟩)
  have ir : i∈R := by simpa only [R,sdiff_singleton_eq_erase] using ((mem_part ..).mp hi).1
  have zi : J.Adj z i := mem_singleton.mp hj ▸ ij.symm
  let L := insert z (C.erase b)
  have eq : univ\L=insert b R := by
    ext a
    by_cases ab : a=b
    · subst a; simp [L,R,S,show b≠z from fun e => zC (e ▸ bC)]
    · simp [L,R,S,ab]
  apply Classical.byContradiction
  intro no
  have cover (a : V) (ha : a∈L) : Dominates J (insert b R) a := by
    rcases mem_insert.mp ha with rfl|ac
    · exact ⟨i,mem_insert_of_mem ir,zi⟩
    by_cases ax : a=x
    · exact ⟨b,mem_insert_self ..,ax ▸ xb⟩
    rcases retained_or_private J C x y z a tip (mem_erase.mpr ⟨ax,mem_of_mem_erase ac⟩) with ⟨t,ht,at'⟩|priv
    · exact ⟨t,mem_insert_of_mem ht,at'⟩
    · have edge : J.Adj b a := by
        apply Classical.byContradiction
        intro missing
        exact no ⟨a,priv,(mem_erase.mp ac).1,missing⟩
      exact ⟨b,mem_insert_self ..,edge.symm⟩
  have len : L.card=C.card := by
    have znot : z∉C.erase b := fun h => zC (mem_of_mem_erase h)
    rw [show L=insert z (C.erase b) from rfl,card_insert_of_not_mem znot,card_erase_add_one bC]
  have score := (score_iff_core J hc hn U C.card).mpr ⟨L,insert_subset zU (erase_subset _ _ |>.trans cu),
    len.ge,eq ▸ joined,fun a ha => eq ▸ cover a ha⟩
  omega

/-- If a failed exchange has just one private leaf, that leaf lies strictly
outside the closed radius-two ball at the failed tip in the lower graph. -/
theorem singleton_far (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (U C : Finset V) (x y z q : V) (xy : x≠y) (cu : C⊆U) (ct : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zu : z∈(U\C).erase y)
    (conn : Con J ((univ\C).erase z)) (fail : ¬SingleWorks J C x y z)
    (only : privateLeaves J C x z={q}) : ¬NearTwo J x q := by
  classical
  obtain side|⟨a,ac,ax,az,unique⟩ := (single_failure_iff J C x y z xy tip
    (mem_sdiff.mp (mem_of_mem_erase zu)).2 (mem_erase.mp zu).1).mp fail
  · exact (side conn).elim
  have ap := (private_iff J C x z a).mpr ⟨ac,az,unique⟩
  have aq := mem_singleton.mp (only ▸ ap)
  subst a
  rintro (qx|xq|⟨b,xb,bq⟩)
  · exact (mem_erase.mp ac).1 qx
  · exact ax xq.symm
  have bC : b∈C := by
    by_contra no
    exact tip.2.2.2.1 ⟨b,mem_sdiff.mpr ⟨mem_univ _,no⟩,xb⟩
  rcases retained_or_private J C x y z b tip (mem_erase.mpr ⟨xb.ne.symm,bC⟩) with dom|priv
  · obtain ⟨a,ha,_,bad⟩ := old_anchor_obstruction J hc hn U C x y z b cu ct tip zu conn xb dom
    exact bad (mem_singleton.mp (only ▸ ha) ▸ bq)
  · exact ax ((mem_singleton.mp (only ▸ priv)) ▸ xb.symm)

#print axioms old_anchor_obstruction
#print axioms singleton_far
end Minimal180.PrivateCore

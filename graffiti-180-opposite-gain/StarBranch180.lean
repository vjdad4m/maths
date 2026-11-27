import StarRepair180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Simultaneously retain all edges at a and give another marked nonroot
vertex t a specified family of children. -/
theorem second_branch (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a t : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (ta : t≠a) (tr : t≠r) (tm : t∈A∪parity G r p) (F : Finset V)
    (sources : ∀ x∈F,x≠r ∧ ¬G.Adj a x ∧ x≠a ∧ G.Adj x t)
    (levels : ∀ x∈F,G.dist t r≤G.dist x r ∨
      (G.Adj a t ∧ G.dist t r=G.dist a r ∧ G.dist t r≤G.dist x r+1))
    (safe : ∀ x∈F,x∉A∩parity G r p) :
    (G.degree a-2)+(F.card-1)≤allowance G r p A := by
  classical
  obtain ⟨T,q,k,sub,tree,down,take,deg,pres,pay⟩ :=
    star_parents G gc r a t ar p A ai am F sources levels (fun x m hit => (safe x m hit).elim)
  have cost := parent_gain G T gc hn sub tree r p A ai q k down take pay ∅ (by simp)
  rw [card_empty,zero_add] at cost
  have ft := parent_neighbors T tree r q k down take t tr
  have fi : F⊆(univ.erase r).filter (fun x => q x=t) := fun x mem =>
    mem_filter.mpr ⟨mem_erase.mpr ⟨(sources x mem).1,mem_univ _⟩,pres x mem⟩
  have smaller := card_le_card fi
  have atmem : a∈(A∪parity G r p).erase r := mem_erase.mpr ⟨ar,mem_union_left _ am⟩
  have otmem : t∈((A∪parity G r p).erase r).erase a := mem_erase.mpr ⟨ta,mem_erase.mpr ⟨tr,tm⟩⟩
  have br := single_le_sum (f:=fun x => T.degree x-2) (fun _ _ => Nat.zero_le _) otmem
  have e := add_sum_erase ((A∪parity G r p).erase r) (fun x => T.degree x-2) atmem
  change T.degree t-2≤∑ v∈((A∪parity G r p).erase r).erase a,(T.degree v-2) at br
  change T.degree a-2+(∑ v∈((A∪parity G r p).erase r).erase a,(T.degree v-2))=
    ∑ v∈(A∪parity G r p).erase r,(T.degree v-2) at e
  omega

/-- At saturation a same-parity neighbor of a has at most one
opposite-parity neighbor outside the star of a. -/
theorem horizontal_port (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a t : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (ap : a∈parity G r p) (at' : G.Adj a t) (tp : t∈parity G r p)
    (sat : G.degree a=allowance G r p A+2) :
    ((G.neighborFinset t).filter (fun x => x∉parity G r p ∧ ¬G.Adj a x)).card≤1 := by
  classical
  let F := (G.neighborFinset t).filter (fun x => x∉parity G r p ∧ ¬G.Adj a x)
  have d := eq_dist G gc r a t p at' (iff_of_true ap tp)
  have tr : t≠r := by
    intro eq;subst t;rw [dist_self] at d;exact ar (gc.dist_eq_zero_iff.mp d)
  have prop (x : V) (m : x∈F) : G.Adj t x ∧ x∉parity G r p ∧ ¬G.Adj a x :=
    ⟨(G.mem_neighborFinset ..).mp (mem_filter.mp m).1,(mem_filter.mp m).2⟩
  have src (x : V) (m : x∈F) : x≠r ∧ ¬G.Adj a x ∧ x≠a ∧ G.Adj x t := by
    obtain ⟨ed,np,no⟩ := prop x m
    refine ⟨?_,no,fun eq => np (eq ▸ ap),ed.symm⟩
    intro eq;subst x
    exact no (dist_eq_one_iff_adj.mp (d.trans (dist_eq_one_iff_adj.mpr ed)))
  have lev (x : V) (m : x∈F) : G.dist t r≤G.dist x r ∨
      (G.Adj a t ∧ G.dist t r=G.dist a r ∧ G.dist t r≤G.dist x r+1) := by
    have h := gc.dist_triangle (u:=t) (v:=x) (w:=r)
    rw [dist_eq_one_iff_adj.mpr (prop x m).1] at h
    exact Or.inr ⟨at',d.symm,by omega⟩
  have bound := second_branch G gc hn r a t ar p A ai am at'.ne.symm tr (mem_union_right _ tp) F src lev
    (fun x m hit => (prop x m).2.1 (mem_inter.mp hit).2)
  change F.card≤1;omega

#print axioms second_branch
#print axioms horizontal_port
end Minimal180.OppositeGain

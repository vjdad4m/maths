import NextDegree180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem region_sum (G : SimpleGraph V) (v : V) (C D : Finset V) (dis : Disjoint C D) :
    (G.neighborFinset v∩C).card+(G.neighborFinset v∩D).card≤G.degree v := by
  classical
  have sep : Disjoint (G.neighborFinset v∩C) (G.neighborFinset v∩D) :=
    dis.mono inter_subset_right inter_subset_right
  have inc : (G.neighborFinset v∩C)∪(G.neighborFinset v∩D)⊆G.neighborFinset v :=
    union_subset inter_subset_left inter_subset_left
  have h := card_le_card inc
  simpa only [card_union_of_disjoint sep,card_neighborFinset_eq_degree] using h

theorem mixed_count (G : SimpleGraph V) (a : V) (C : Finset V) (c : V→Bool) (lc : MixedAt G a C c) :
    2≤(G.neighborFinset a∩C).card := by
  classical
  obtain ⟨u,v,au,av,cu,cv,um,vm,_⟩ := lc
  have ne : u≠v := fun e => Bool.noConfusion (cu.symm.trans ((congrArg c e).trans cv))
  have inc : ({u,v}:Finset V)⊆G.neighborFinset a∩C := insert_subset (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr au,um⟩)
    (singleton_subset_iff.mpr (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr av,vm⟩))
  simpa only [card_pair ne] using card_le_card inc

private theorem small_side_flexible (G : SimpleGraph V) (a b : V) (ab : a≠b) (na : ¬G.Adj a b)
    (A K S : Finset V) (ai : Indep G A) (am : a∈A) (ka : K⊆A) (sr : S⊆univ\{a,b})
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (mixed : MixedAt G a S c)
    (ac : (G.neighborFinset a∩S).card≤2) (bc : (G.neighborFinset b∩S).card≤1) :
    ∀ t,DropCheck G a b K S c t := by
  classical
  obtain ⟨u,v,au,av,cu,cv,um,vm,_⟩ := mixed
  have neq : c u≠c v := fun eq => Bool.noConfusion (cu.symm.trans (eq.trans cv))
  have uv : u≠v := fun eq => neq (congrArg c eq)
  have eq : ({u,v}:Finset V)=G.neighborFinset a∩S := eq_of_subset_of_card_le
    (insert_subset (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr au,um⟩)
    (singleton_subset_iff.mpr (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr av,vm⟩))) (by simpa only [card_pair uv] using ac)
  have cover (x : V) (xm : x∈S) (ed : G.Adj a x) : x=u ∨ x=v := by
    have m : x∈({u,v}:Finset V) := eq ▸ mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr ed,xm⟩
    exact (mem_insert.mp m).imp_right mem_singleton.mp
  have mono : ∃ j,∀ x∈S,G.Adj b x → c x=j := by
    by_cases some : (G.neighborFinset b∩S).Nonempty
    · obtain ⟨v,vm⟩ := some
      exact ⟨c v,fun x xm ed => congrArg c (card_le_one.mp bc x (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr ed,xm⟩) v vm)⟩
    · exact ⟨false,fun x xm ed => (some ⟨x,mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr ed,xm⟩⟩).elim⟩
  have ao : a∉S := fun m => (mem_sdiff.mp (sr m)).2 (mem_insert_self ..)
  have bo : b∉S := fun m => (mem_sdiff.mp (sr m)).2 (mem_insert_of_mem (mem_singleton_self _))
  have ok : ProperOn G S c := fun x xm y ym => cp x (sr xm) y (sr ym)
  obtain ⟨j,one⟩ := mono
  intro t
  obtain ⟨x,xm,xk,col⟩ := flexible_contact G a b ab na S K ao bo c ok u v um vm
    (fun m => ai a am u (ka m) au.ne au) (fun m => ai a am v (ka m) av.ne av) neq cover j one t
  exact ⟨x,xm,xk,(terminal_iff_contacts G a b ab na _ (fun m => ao (mem_of_mem_erase m))
    (fun m => bo (mem_of_mem_erase m)) c (fun i im k km => ok i (mem_of_mem_erase im) k (mem_of_mem_erase km)) t).mp col⟩

/-- If both terminal masks are nonempty and disjoint, each active region
must contain at least two contacts of the second tip. -/
theorem opposite_contacts (G : SimpleGraph V) (a b : V) (ab : a≠b) (na : ¬G.Adj a b)
    (A K : Finset V) (ai : Indep G A) (am : a∈A) (ka : K⊆A) (deg : G.degree a=4)
    (C D O : Finset V) (h : TwoRegions G a b C D O) (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c)
    (lc : MixedAt G a C c) (rc : MixedAt G a D c)
    (left : ∃ t,DropCheck G a b K C c t) (right : ∃ t,DropCheck G a b K D c t)
    (apart : ¬∃ t,DropCheck G a b K C c t ∧ DropCheck G a b K D c t) :
    2≤(G.neighborFinset b∩C).card ∧ 2≤(G.neighborFinset b∩D).card ∧ 4≤G.degree b := by
  classical
  have total := region_sum G a C D h.apart
  have l := mixed_count G a C c lc
  have d := mixed_count G a D c rc
  have cs : C⊆univ\({a,b}:Finset V) := h.partition ▸ subset_union_left.trans subset_union_left
  have ds : D⊆univ\({a,b}:Finset V) := h.partition ▸ subset_union_right.trans subset_union_left
  have cl : 2≤(G.neighborFinset b∩C).card := by
    by_contra! low
    obtain ⟨t,r⟩ := right
    exact apart ⟨t,small_side_flexible G a b ab na A K C ai am ka cs c cp lc (by omega) (by omega) t,r⟩
  have dl : 2≤(G.neighborFinset b∩D).card := by
    by_contra! low
    obtain ⟨t,q⟩ := left
    exact apart ⟨t,q,small_side_flexible G a b ab na A K D ai am ka ds c cp rc (by omega) (by omega) t⟩
  exact ⟨cl,dl,by have := region_sum G b C D h.apart;omega⟩

/-- With genuinely opposite, nonempty terminal masks and no nonroot
independent mark of degree two, the only possible exceptional second-tip location
at allowance two is exactly two layers beyond the protected tip. -/
theorem opposite_forces_three (G : SimpleGraph V) (gc : G.Connected) (r a b : V) (ar : a≠r)
    (p : Bool) (A : Finset V) (ai : Indep G A) (ab : a≠b) (na : ¬G.Adj a b)
    (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p)) (bk : b∉A∩insert r (parity G r p))
    (deg : G.degree a=4) (C D O : Finset V) (h : TwoRegions G a b C D O)
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (lc : MixedAt G a C c) (rc : MixedAt G a D c)
    (left : ∃ t,DropCheck G a b (A∩insert r (parity G r p)) C c t)
    (right : ∃ t,DropCheck G a b (A∩insert r (parity G r p)) D c t)
    (absent : ¬∃ t,DropCheck G a b (A∩insert r (parity G r p)) C c t ∧
       DropCheck G a b (A∩insert r (parity G r p)) D c t)
    (high : ∀ v∈A,v≠r → G.degree v≠2) (distance : G.dist b r≠G.dist a r+2) : 3≤allowance G r p A := by
  classical
  have hi : 2<Fintype.card V := by have := G.degree_lt_card_verts a;omega
  have am := (mem_inter.mp ak).1
  have ap := (mem_insert.mp (mem_inter.mp ak).2).resolve_left ar
  have paid := protected_degree G gc hi r a p A ai ak
  have db := (opposite_contacts G a b ab na A _ ai am inter_subset_left deg C D O h c cp lc rc left right absent).2.2
  by_contra! small
  have sat : G.degree a=allowance G r p A+2 := by omega
  have avoid : TipAvoids G r a b p A := by
    by_cases next : G.dist b r=G.dist a r+1
    · apply Or.inl
      intro hit
      rcases mem_union.mp hit with bm|bp
      · have cap := next_degree G gc hi r a b ar p A ai am ap bm deg sat next;omega
      · have e := (mem_parity ..).mp bp
        have f := (mem_parity ..).mp ap
        omega
    · exact Or.inr ⟨next,distance⟩
  have force := masks_force_three G gc r a b ar p A ai ab na bi ak bk deg C D O h c cp lc rc (Or.inr ⟨high,avoid⟩) absent
  omega

#print axioms region_sum
#print axioms mixed_count
#print axioms opposite_contacts
#print axioms opposite_forces_three
end Minimal180.OppositeGain

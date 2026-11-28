import SixNearOrderSixteen189
import ResidualOreParam189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private def joinAcross (J : SimpleGraph V) (P Q : Finset V) : SimpleGraph V where
  Adj x y := J.Adj x y ∨ (x≠y ∧ ((x∈P ∧ y∈Q) ∨ (y∈P ∧ x∈Q)))
  symm := fun _ _ h=>h.elim (fun e=>.inl e.symm) (fun e=>.inr ⟨e.1.symm,e.2.symm⟩)
  loopless := fun x h=>h.elim (J.loopless x) (fun h=>h.1 rfl)

private instance (J : SimpleGraph V) [DecidableRel J.Adj] (P Q : Finset V) :
    DecidableRel (joinAcross J P Q).Adj := fun _ _=>inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

/-- A seven-vertex block with at least five core vertices of local degree at
least five becomes Hamilton-connected if each other vertex has local
degree at least three. Only cross-edges to the core need be completed. -/
theorem dark_block_seven_hamilton_connected (D S : Finset V) (sub : S⊆D)
    (d7 : D.card=7) (s5 : 5≤S.card)
    (strict : ∀ z∈S,5≤(inside G D z).card)
    (other : ∀ z∈D,z∉S → 3≤(inside G D z).card)
    {x y : V} (xd : x∈D) (yd : y∈D) (xy : x≠y) :
    RouteOn G D x y := by
  classical
  let U := ↑(↑D : Set V)
  let J := G.induce (↑D : Set V)
  let A : Finset U := univ.filter (fun z=>z.val∈S)
  let B : Finset U := univ\A
  let H := joinAcross J A B
  have n : Fintype.card U=7 := (Fintype.card_coe D).trans d7
  have ea (z : U) : z∈A ↔ z.val∈S := by simp [A]
  have eb (z : U) : z∈B ↔ z.val∉S := by simp [B,ea]
  have A5 : 5≤A.card := by
    have e : (S : Finset V).card=A.card := by
      apply card_bij (fun z zz=>(⟨z,sub zz⟩ : U))
      · intro z zz
        exact (ea _).mpr zz
      · intro z _ w _ h
        exact congrArg Subtype.val h
      · intro z za
        exact ⟨z.val,(ea _).mp za,rfl⟩
    omega
  have jA {u : U} (ua : u∈A) : 5≤J.degree u := by
    rw [←inside_card_eq_degree_induce (G:=G) D u]
    exact strict u.val ((ea u).mp ua)
  have jB {u : U} (ub : u∈B) : 3≤J.degree u := by
    rw [←inside_card_eq_degree_induce (G:=G) D u]
    exact other u.val u.property ((eb u).mp ub)
  have incl : J≤H := fun _ _ h=>.inl h
  have closure_budget (u v : U) (uv : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card U+1≤J.degree u+J.degree v := by
    rcases uv with uv|⟨_,⟨ua,vb⟩|⟨va,ub⟩⟩
    · exact (no uv).elim
    · have i := jA ua
      have j := jB vb
      omega
    have i := jA va
    have j := jB ub
    omega
  have minH (u : U) : 5≤H.degree u := by
    by_cases ua : u∈A
    · have p := jA ua
      have w : J.neighborFinset u⊆H.neighborFinset u := fun _ h=>
        (mem_neighborFinset _ _ _).mpr (incl ((mem_neighborFinset _ _ _).mp h))
      have q := card_le_card w
      rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at q
      omega
    have ub : u∈B := mem_sdiff.mpr ⟨mem_univ _,ua⟩
    have ss : A⊆H.neighborFinset u := by
      intro v va
      exact (mem_neighborFinset _ _ _).mpr (.inr ⟨fun e=>ua (e.symm ▸ va),.inr ⟨va,ub⟩⟩)
    have p := card_le_card ss
    rw [card_neighborFinset_eq_degree] at p
    omega
  let x' : U := ⟨x,xd⟩
  let y' : U := ⟨y,yd⟩
  have xy' : x'≠y' := fun e=>xy (congrArg Subtype.val e)
  obtain ⟨p,pp,ps⟩ := hamilton_connected_of_ore (G:=H)
    (fun u v _ _=>by have u' := minH u; have v' := minH v; change Fintype.card U+1≤H.degree u+H.degree v; omega) xy'
  obtain ⟨q,qp,qs⟩ := terminal_ore_closure incl closure_budget p pp ps
  exact lift_side_path D q qp qs

private theorem erase_internal_deg (D : Finset V) (w z : V) :
    (inside G D z).card≤(inside G (D.erase w) z).card+1 := by
  have eq : inside G (D.erase w) z=(inside G D z).erase w := by
    ext u
    simp only [inside,mem_filter,mem_erase]
    tauto
  rw [eq]
  have k := card_erase_le (s:=inside G D z) (a:=w)
  by_cases e : w∈inside G D z
  · have q := card_erase_add_one e
    omega
  rw [erase_eq_of_not_mem e]
  omega

/-- Removing a low balanced point leaves a Hamilton-connected subblock.
At most two points can be outside the strict degree-five class. -/
theorem dark_block_remove_low_hamilton_connected (D S : Finset V) (sub : S⊆D)
    (d7 : D.card=7) (s5 : 5≤S.card)
    (strict : ∀ z∈S,5≤(inside G D z).card)
    {w x y : V} (wd : w∈D) (wn : w∉S) (low : (inside G D w).card≤2)
    (xd : x∈D.erase w) (yd : y∈D.erase w) (xy : x≠y) :
    RouteOn G (D.erase w) x y := by
  classical
  let W := D\S
  have wW : w∈W := mem_sdiff.mpr ⟨wd,wn⟩
  have sz : (D.erase w).card=6 := by rw [card_erase_of_mem wd,d7]
  have w2 : W.card≤2 := by
    change (D\S).card≤2
    rw [card_sdiff sub,d7]
    omega
  have strict4 {z : V} (zm : z∈S) : 4≤(inside G (D.erase w) z).card := by
    have b := erase_internal_deg (G:=G) D w z
    have q := strict z zm
    omega
  have bal3 {v : V} (vm : v∈D.erase w) (vs : v∉S) :
      3≤(inside G (D.erase w) v).card := by
    have ⟨vw,vd⟩ := mem_erase.mp vm
    have vW : v∈W := mem_sdiff.mpr ⟨vd,vs⟩
    have e : W={w,v} := by
      have p : ({w,v}:Finset V)⊆W := insert_subset wW (singleton_subset_iff.mpr vW)
      exact (eq_of_subset_of_card_le p (by simpa [vw.symm] using w2)).symm
    let A := S.filter (G.Adj w)
    let B := S.filter (G.Adj v)
    have all : S⊆A∪B := by
      intro z zm
      have h := strict z zm
      by_cases wz : G.Adj w z
      · exact mem_union_left _ (mem_filter.mpr ⟨zm,wz⟩)
      by_cases vz : G.Adj v z
      · exact mem_union_right _ (mem_filter.mpr ⟨zm,vz⟩)
      have cover : inside G D z⊆S.erase z := by
        intro u uu
        have ⟨ud,zu⟩ := mem_filter.mp uu
        by_cases us : u∈S
        · exact mem_erase.mpr ⟨zu.ne.symm,us⟩
        have uw : u∈W := mem_sdiff.mpr ⟨ud,us⟩
        rw [e] at uw
        rcases (by simpa using uw : u=w ∨ u=v) with rfl|rfl
        · exact (wz zu.symm).elim
        exact (vz zu.symm).elim
      have p := card_le_card cover
      rw [card_erase_of_mem zm] at p
      have Wcard : W.card=2 := by rw [e,card_insert_of_not_mem (by simp [vw.symm]),card_singleton]
      have ss : S.card=5 := by
        change (D\S).card=2 at Wcard
        rw [card_sdiff sub,d7] at Wcard
        omega
      omega
    have aa : A⊆inside G D w := fun _ h=>
      mem_filter.mpr ⟨sub (mem_filter.mp h).1,(mem_filter.mp h).2⟩
    have bb : B⊆inside G (D.erase w) v := fun u h=>mem_filter.mpr
      ⟨mem_erase.mpr ⟨fun e=>wn (e ▸ (mem_filter.mp h).1),sub (mem_filter.mp h).1⟩,
        (mem_filter.mp h).2⟩
    have k := card_le_card all
    have l := card_union_le A B
    have m := card_le_card aa
    have n := card_le_card bb
    omega
  apply terminal_route_on_of_local_ore (D.erase w) xd yd xy
  intro u ud v vd ne _
  by_cases us : u∈S
  · have a := strict4 us
    by_cases vs : v∈S
    · have b := strict4 vs
      omega
    have b := bal3 vd vs
    omega
  have a := bal3 ud us
  by_cases vs : v∈S
  · have b := strict4 vs
    omega
  exfalso
  have uW : u∈W := mem_sdiff.mpr ⟨(mem_erase.mp ud).2,us⟩
  have vW : v∈W := mem_sdiff.mpr ⟨(mem_erase.mp vd).2,vs⟩
  have i : ({u,v,w}:Finset V)⊆W := insert_subset uW (insert_subset vW (singleton_subset_iff.mpr wW))
  have c := card_le_card i
  have c3 : ({u,v,w}:Finset V).card=3 := card_eq_three.mpr
    ⟨u,v,w,ne,(mem_erase.mp ud).1,(mem_erase.mp vd).1,rfl⟩
  omega

#print axioms dark_block_seven_hamilton_connected
#print axioms dark_block_remove_low_hamilton_connected
end Graffiti189LongestPath.CrossSaturation.ThresholdSix

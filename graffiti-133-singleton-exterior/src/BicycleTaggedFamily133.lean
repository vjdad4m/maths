import BicycleTaggedChannels133

namespace Graffiti133Bicycle
open SimpleGraph Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure TaggedFamily (G : SimpleGraph V) (B : Finset V) where
  sets : Finset (Finset V)
  avoid : ∀ S∈sets, Disjoint S B
  cover : ∀ x∉B, ∃ S∈sets,x∈S
  separate : ∀ S∈sets, ∀ T∈sets,S≠T → Disjoint S T
  noEdges : ∀ S∈sets, ∀ T∈sets,S≠T → ∀ x∈S, ∀ y∈T, ¬G.Adj x y
  head : (S : {S // S∈sets}) → V
  head_mem : ∀ S, head S∈B
  channel : ∀ S : {S // S∈sets}, TaggedChannel G B S.val (head S)

theorem tag_all_degree_two_components [DecidableRel G.Adj]
    (hc : G.Connected) (B : Finset V) (bne : B.Nonempty)
    (degree : ∀ x∉B,G.degree x=2) :
    Nonempty (TaggedFamily G B) := by
  classical
  let Good (S : Finset V) : Prop :=
    S.Nonempty ∧ Disjoint S B ∧ (G.induce (S : Set V)).Connected ∧
      ∀ x∈S, ∀ y∉B, G.Adj x y → y∈S
  let Fam := Finset.univ.filter Good
  have OK (S : Finset V) (h : S∈Fam) : Good S := (Finset.mem_filter.mp h).2
  have avoid (S : Finset V) (h : S∈Fam) : Disjoint S B := (OK S h).2.1
  have close (S : Finset V) (h : S∈Fam) : ∀ x∈S, ∀ y∉B, G.Adj x y → y∈S := (OK S h).2.2.2
  have cover (x : V) (off : x∉B) : ∃ S∈Fam,x∈S := by
    obtain ⟨S,hx,sep,conn,closed⟩ := component_after_removing B x off
    exact ⟨S,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨x,hx⟩,sep,conn,closed⟩⟩,hx⟩
  have apart (S : Finset V) (sF : S∈Fam) (T : Finset V) (tF : T∈Fam)
      (ne : S≠T) : Disjoint S T := by
    by_cases notSub : ∃ u∈T,u∉S
    · obtain ⟨u,ut,us⟩ := notSub
      exact disjoint_component_of_outside_anchor B S T (close S sF) (avoid T tF)
        (OK T tF).2.2.1 ut us
    · have lr : T⊆S := fun x ht => by by_contra hs; exact notSub ⟨x,ht,hs⟩
      have other : ∃ u∈S,u∉T := by
        by_contra! no
        exact ne (Finset.Subset.antisymm no lr)
      obtain ⟨u,us,ut⟩ := other
      exact (disjoint_component_of_outside_anchor B T S (close T tF) (avoid S sF)
        (OK S sF).2.2.1 us ut).symm
  have noEdges (S : Finset V) (sF : S∈Fam) (T : Finset V) (tF : T∈Fam)
      (ne : S≠T) (x : V) (hx : x∈S) (y : V) (hy : y∈T) : ¬G.Adj x y := by
    intro e
    have yoff : y∉B := fun hb=>Finset.disjoint_left.mp (avoid T tF) hy hb
    exact Finset.disjoint_left.mp (apart S sF T tF ne) (close S sF x hx y yoff e) hy
  have enters (S : Finset V) (h : S∈Fam) : ∃ a∈B, ∃ p∈S,G.Adj p a := by
    obtain ⟨x,hx⟩ := (OK S h).1
    obtain ⟨b,hb⟩ := bne
    obtain ⟨p⟩ := hc x b
    by_contra no
    have step (x y : V) (hx : x∈S) (e : G.Adj x y) : y∈S := by
      by_cases hy : y∈B
      · exact (no ⟨y,hy,x,hx,e⟩).elim
      · exact close S h x hx y hy e
    have all : ∀ {x y : V}, G.Walk x y → x∈S → y∈S := by
      intro x y q
      induction q with
      | nil => exact id
      | @cons u w v e q ih => exact fun hh=>ih (step u w hh e)
    exact Finset.disjoint_left.mp (avoid S h) (all p hx) hb
  have tags (S : {S // S∈Fam}) : ∃ a∈B, Nonempty (TaggedChannel G B S.val a) := by
    obtain ⟨a,ha,p,hp,e⟩ := enters _ S.property
    refine ⟨a,ha,tag_degree_two_channel B S.val (avoid _ S.property) (OK _ S.property).2.2.1
      (fun x hx => degree x (fun hb => Finset.disjoint_left.mp (avoid _ S.property) hx hb))
      (close _ S.property) ha hp e⟩
  let hd (S : {S // S∈Fam}) := Classical.choose (tags S)
  have hp (S : {S // S∈Fam}) := Classical.choose_spec (tags S)
  exact ⟨⟨Fam,avoid,cover,apart,noEdges,hd,fun S=>(hp S).1,fun S=>Classical.choice (hp S).2⟩⟩

#print axioms tag_all_degree_two_components
end Graffiti133Bicycle

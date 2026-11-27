import P5CoreShape133

namespace Graffiti133P5CoreShape
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def UniqueAnchor (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ x, x∉C → ∃ a∈C, ∀ b∈C, G.Adj x b ↔ b=a

theorem singleton_anchor_large_clique (h4 : FourCycleFree G)
    (C : Finset V) (cd : CD G C) (cl : G.IsClique (C : Set V)) (hC : 3≤C.card) :
    UniqueAnchor G C := by
  intro x xo
  rcases cd.2 x with xm|⟨a,am,xa⟩
  · exact (xo xm).elim
  refine ⟨a,am,fun b bm=>⟨?_,fun e=>e.symm ▸ xa⟩⟩
  intro xb
  by_contra ne
  have there : ∃ z∈C,z≠a ∧ z≠b := by
    by_contra! no
    have sub : C⊆({a,b} : Finset V) := by
      intro z zm
      rw [Finset.mem_insert,Finset.mem_singleton]
      by_cases za : z=a
      · exact Or.inl za
      · exact Or.inr (no z zm za)
    have cap := Finset.card_le_card sub
    rw [Finset.card_pair (Ne.symm ne)] at cap
    omega
  obtain ⟨z,zm,za,zb⟩ := there
  have ez := h4 x z a b (fun e=>xo (e.symm ▸ zm)) xa (cl zm am za) xb (cl zm bm zb)
  exact ne ez.symm

theorem dominating_clique_normalizes_anchor (h4 : FourCycleFree G)
    (C : Finset V) (cd : CD G C) (cl : G.IsClique (C : Set V)) :
    ∃ A : Finset V,C⊆A ∧ CD G A ∧ G.IsClique (A : Set V) ∧ UniqueAnchor G A := by
  classical
  by_cases all : UniqueAnchor G C
  · exact ⟨C,Subset.rfl,cd,cl,all⟩
  have small : C.card≤2 := by
    by_contra! large
    exact all (singleton_anchor_large_clique h4 C cd cl large)
  have positive : 0<C.card := by
    obtain ⟨p⟩ := cd.1.nonempty
    exact Finset.card_pos.mpr ⟨p.val,p.property⟩
  have two : C.card=2 := by
    by_contra ne
    have one : C.card=1 := by omega
    obtain ⟨a,ah⟩ := Finset.card_eq_one.mp one
    apply all
    intro x xo
    have am : a∈C := by simp [ah]
    rcases cd.2 x with insane|⟨b,bm,xb⟩
    · exact (xo insane).elim
    · refine ⟨a,am,fun z zm=>?_⟩
      have e : z=a := by simpa [ah] using zm
      have d : b=a := by simpa [ah] using bm
      exact ⟨fun _=>e,fun _=>e.symm ▸ d ▸ xb⟩
  obtain ⟨a,b,ab,cover⟩ := Finset.card_eq_two.mp two
  have pair : ∃ x,x∉C ∧ G.Adj x a ∧ G.Adj x b := by
    by_contra! no
    apply all
    intro x xo
    rcases cd.2 x with insane|⟨z,zm,xz⟩
    · exact (xo insane).elim
    refine ⟨z,zm,fun w wm=>⟨?_,fun e=>e.symm ▸ xz⟩⟩
    intro xw
    have wz : w=a ∨ w=b := by simpa [cover] using wm
    have zz : z=a ∨ z=b := by simpa [cover] using zm
    rcases wz with rfl|rfl <;> rcases zz with rfl|rfl
    · rfl
    · exact (no x xo xw xz).elim
    · exact (no x xo xz xw).elim
    · rfl
  obtain ⟨x,xo,xa,xb⟩ := pair
  let A := insert x C
  have Csub : C⊆A := Finset.subset_insert _ _
  have xEdges (y : V) (ym : y∈C) : G.Adj x y := by
    have alt : y=a ∨ y=b := by simpa [cover] using ym
    rcases alt with e|e
    · exact e.symm ▸ xa
    · exact e.symm ▸ xb
  have acl : G.IsClique (A : Set V) := by
    intro y ym z zm yz
    rcases Finset.mem_insert.mp ym with ye|ye <;> rcases Finset.mem_insert.mp zm with ze|ze
    · exact (yz (ye.trans ze.symm)).elim
    · exact ye.symm ▸ xEdges z ze
    · exact ze.symm ▸ (xEdges y ye).symm
    · exact cl ye ze yz
  have acd : CD G A := by
    constructor
    · rw [connected_iff_exists_forall_reachable]
      let xA : (A : Set V) := ⟨x,Finset.mem_insert_self _ _⟩
      refine ⟨xA,fun y=>?_⟩
      by_cases eq : xA=y
      · exact eq ▸ SimpleGraph.Reachable.refl xA
      · exact (show (G.induce (A : Set V)).Adj xA y from
          acl xA.property y.property (fun e=>eq (Subtype.ext e))).reachable
    · intro y
      exact (cd.2 y).imp (fun m=>Csub m) (fun ⟨z,zm,yz⟩=>⟨z,Csub zm,yz⟩)
  have size : 3≤A.card := by
    change 3≤(insert x C).card
    rw [Finset.card_insert_of_not_mem xo,two]
  exact ⟨A,Csub,acd,acl,singleton_anchor_large_clique h4 A acd acl size⟩

theorem anchors_equal_across_exterior_edge (h4 : FourCycleFree G)
    (C : Finset V) (cl : G.IsClique (C : Set V))
    {x y a b : V} (xo : x∉C) (yo : y∉C) (am : a∈C) (bm : b∈C)
    (xa : G.Adj x a) (yb : G.Adj y b) (xy : G.Adj x y) : a=b := by
  by_contra ne
  have h := h4 a y x b (fun e=>yo (e ▸ am)) xa.symm xy.symm (cl am bm ne) yb
  exact xo (h.symm ▸ bm)

theorem exterior_matching (h4 : FourCycleFree G) (C : Finset V)
    (cl : G.IsClique (C : Set V)) (uniq : UniqueAnchor G C)
    {x y z : V} (xo : x∉C) (yo : y∉C) (zo : z∉C)
    (xy : G.Adj x y) (xz : G.Adj x z) : y=z := by
  obtain ⟨a,am,xa⟩ := uniq x xo
  obtain ⟨b,bm,yb⟩ := uniq y yo
  obtain ⟨c,cm,zc⟩ := uniq z zo
  have xh := (xa a am).mpr rfl
  have yh := (yb b bm).mpr rfl
  have zh := (zc c cm).mpr rfl
  have ab := anchors_equal_across_exterior_edge h4 C cl xo yo am bm xh yh xy
  have ac := anchors_equal_across_exterior_edge h4 C cl xo zo am cm xh zh xz
  exact h4 x a y z (fun e=>xo (e.symm ▸ am)) xy (ab.symm ▸ yh.symm) xz (ac.symm ▸ zh.symm)

theorem p5free_C4free_core_shape (hc : G.Connected) (h4 : FourCycleFree G) (h5 : NoPath G 5) :
    (∃ H : Hole G 5,Function.Surjective H.c) ∨
    ∃ A : Finset V,CD G A ∧ G.IsClique (A : Set V) ∧ UniqueAnchor G A ∧
      (∀ x y z, x∉A → y∉A → z∉A → G.Adj x y → G.Adj x z → y=z) := by
  rcases p5free_C4free_clique_or_spanning_C5 hc h4 h5 with ⟨C,cd,cl⟩|five
  · obtain ⟨A,_,d,a,u⟩ := dominating_clique_normalizes_anchor h4 C cd cl
    exact Or.inr ⟨A,d,a,u,fun x y z=>exterior_matching h4 A a u⟩
  · exact Or.inl five

#print axioms p5free_C4free_core_shape
end Graffiti133P5CoreShape
